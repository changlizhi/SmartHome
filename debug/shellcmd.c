/**
* shellcmd.c -- �����е�������
* 
* ����: yangzhilong
* ����ʱ��: 2009-10-30
* ����޸�ʱ��: 2009-10-30
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "include/basetype.h"
#include "include/debug.h"
#include "include/version.h"
#include "include/debug/shellcmd.h"
#include "include/sys/schedule.h"
#include "include/sys/timeal.h"
#include "include/sys/reset.h"
#include "include/sys/timer.h"
#include "include/sys/gpio.h"
#include "include/sys/rs485.h"
#include "include/sys/cycsave.h"
#include "include/param/unique.h"
#include "include/param/term.h"
#include "include/lib/align.h"

extern void GetOneInterval( int startime, char* tmpline, int m, int n );

static int shell_debug(int argc, char *argv[])
{
	int type;

	if(argc != 2) return 1;

	type = atoi(argv[1]);
	if(argc < 0 || argc > 30) return 1;
	SetLogType(type);
	if(type) PrintLog(0, "open debug %d ok\n", type);
	else {
		PrintLog(0, "close debug ok\n");
		SetLogInterface(0);
	}
	return 0;
}
DECLARE_SHELL_CMD("debug", shell_debug, "�ı���Դ�ӡ����");

static int shell_showtime(int argc, char *argv[])
{
	sysclock_t clock;
	const char *pstr;

	SysClockRead(&clock);
	pstr = SysClockFormat(&clock);
	PrintLog(0, "��ǰʱ��: %s\n", pstr);
	return 0;
}
DECLARE_SHELL_CMD("time", shell_showtime, "��ʾ��ǰʱ��");

static int shell_showclock(int argc, char *argv[])
{
	sysclock_t clock;
	const char *pstr;
	extclock_t extclock;

	if(ExtClockRead(&extclock)) {
		PrintLog(0, "read ext clock fail\n");
		return 1;
	}

	clock.year = extclock.year;
	clock.month = extclock.month;
	clock.day = extclock.day;
	clock.hour = extclock.hour;
	clock.minute = extclock.minute;
	clock.second = extclock.second;
	clock.week = extclock.week;

	SysClockRead(&clock);
	pstr = SysClockFormat(&clock);
	PrintLog(0, "��ǰʱ��: %s\n", pstr);
	return 0;
}
DECLARE_SHELL_CMD("clock", shell_showclock, "��ʾ��ǰʵʱʱ��");

static int shell_restart(int argc, char *argv[])
{
	PrintLog(0, "ϵͳ���ڸ�λ, ��ȴ�...\n");
	#ifdef DEBUGMODE
	SaveParam();
	#endif
	SysRestart();
	return 0;
}
DECLARE_SHELL_CMD("reboot", shell_restart, "��λ�ն�");

static int shell_settime(int argc, char *argv[])
{
	int i;
	sysclock_t clock;
	utime_t utime, utimecur;
	extclock_t extclock;

	if(argc != 7) return 1;

	i = atoi(argv[1]);
	if(i < 0 || i > 99) {
		PrintLog(0, "invalid year\n");
		return 1;
	}
	clock.year = i;

	i = atoi(argv[2]);
	if(i < 1 || i > 12) {
		PrintLog(0, "invalid month\n");
		return 1;
	}
	clock.month = i;

	i = atoi(argv[3]);
	if(i < 1 || i > 31) {
		PrintLog(0, "invalid day\n");
		return 1;
	}
	clock.day = i;

	i = atoi(argv[4]);
	if(i < 0 || i > 23) {
		PrintLog(0, "invalid hour\n");
		return 1;
	}
	clock.hour = i;

	i = atoi(argv[5]);
	if(i < 0 || i > 59) {
		PrintLog(0, "invalid minute\n");
		return 1;
	}
	clock.minute = i;

	i = atoi(argv[6]);
	if(i < 0 || i > 59) {
		PrintLog(0, "invalid second\n");
		return 1;
	}
	clock.second = i;

	utimecur = UTimeReadCurrent();
	utime = SysClockToUTime(&clock);

	DebugPrint(0, "set sys clock to %s\n", SysClockFormat(&clock));
	SysClockSet(&clock);
	SysClockRead(&clock);
	DebugPrint(0, "set ext clock to %s\n", SysClockFormat(&clock));

	extclock.century = 0;
	extclock.year = clock.year;
	extclock.month = clock.month;
	extclock.day = clock.day;
	extclock.hour = clock.hour;
	extclock.minute = clock.minute;
	extclock.second = clock.second;
	extclock.week = clock.week;

	ExtClockWrite(&extclock);

	if(utimecur > utime) i = utimecur - utime;
	else i = utime - utimecur;

	if(i > 300) SysRecalAllRTimer();

	PrintLog(0, "�����ն�ʱ��ɹ�\n");
	return 0;
}
DECLARE_SHELL_CMD("settime", shell_settime, "�����ն�ʱ��");


static void rs485_looptest(int porta, int portb, int baud)
{
	int i, j, idx, porttmp;
	unsigned char buf[48];

	Rs485Lock(porta);
	Rs485Lock(portb);

	Rs485Set(porta, baud, 8, 1, 'e');
	Rs485Set(portb, baud, 8, 1, 'e');
	
	for(idx=0; idx<2; idx++) 
	{
		while(Rs485Recv(portb, buf, 32) > 0);
		
		for(i=0; i<32; i++) buf[i] = i;

		Rs485Send(porta, buf, 32);
		Sleep(150);
		
		i = Rs485Recv(portb, buf, 48);
		//PrintLog(0, "port%d rcv%dbytes\n", portb, i);
		if(i <= 0) {
			PrintLog(0, "��·����%d->%d %dpbsʧ��\n", porta, portb, baud);
			goto reverse;
		}

		if(i < 32) PrintLog(0, "too short\n");
		else i = 32;

		for(j=0; j<i; j++) 
		{
			if(buf[j] != (unsigned char)j) PrintLog(0, "��%d���ֽڲ���\n", j);
		}
		if(j >= 32) PrintLog(0, "��·����%d->%d %dbps�ɹ�\n", porta, portb, baud);
		else PrintLog(0, "��·����%d->%d %dbpsʧ��\n", porta, portb, baud);
		
reverse:
		porttmp = porta;
		porta = portb;
		portb = porttmp;
	}

	/*by ydl add 2011-04-12:�ָ��˿�Ĭ�ϲ���(�����޶�ȡ�˿ڲ���������ʱ������)*/
	Rs485Set(porta, 1200, 8, 1, 'e');
	Rs485Set(portb, 1200, 8, 1, 'e');
	
	Rs485Unlock(porta);
	Rs485Unlock(portb);
}

 
static int shell_rs485test(int argc, char *argv[])
{
	int porta, portb;

	PrintLog(0, "Rs485��·���Կ�ʼ\r\n");
	
	porta = 0;
	portb = 1;
	rs485_looptest(porta, portb, 300);
	rs485_looptest(porta, portb, 1200);
	rs485_looptest(porta, portb, 2400);
	rs485_looptest(porta, portb, 9600);

	porta = 0;
	portb = 2;
	rs485_looptest(porta, portb, 300);
	rs485_looptest(porta, portb, 1200);
	rs485_looptest(porta, portb, 2400);
	rs485_looptest(porta, portb, 9600);

	PrintLog(0, "Rs485��·���Խ���\r\n");
	return 0;
}
DECLARE_SHELL_CMD("rs485", shell_rs485test, "RS485��·����");
 
#ifdef DEBUGMODE
extern void ReadPlcMetImp(unsigned short metpos);
static int shell_readimp(int argc, char *argv[])
{
	if (argc < 3)
	{
		PrintLog( 0, "Invalid Paramater Number!\n");
		return 1;
	}
	
	int startmid, num;
	startmid = atoi(argv[1]);
	num = atoi(argv[2]);
	if (startmid < IMPORTANT_BASEMETP || startmid > IMPORTANT_ENDMETP)
	{
		PrintLog( 0, "Invalid Paramater:startmid!\n");
		return 1;
	}
	if (num == 0 || num > MAX_IMPORTANT_USER || (startmid+num) > (IMPORTANT_ENDMETP+1) )
	{
		PrintLog( 0, "Invalid Paramater:num!\n");
		return 1;
	}

	PrintLog(0, "start read!\r\n");
	while(num--)
	{
		if(0==ParaMeterG[startmid].flag ||0xFF==ParaMeterG[startmid].flag) 
		{	
			PrintLog(0, "mid:%d invalid!\r\n", startmid);
			continue;
		}
		
		ReadPlcMetImp(startmid++);	
	}
	PrintLog(0, "end read!\r\n");

	return 0;
}
DECLARE_SHELL_CMD("readimp", shell_readimp, "��ȡ�ص��û�����");
#endif



static int shell_sysinfo(int argc, char *argv[])
{

	sysclock_t clock;
	const char *pstr;

	GetClockSysStart(&clock);

	pstr = SysClockFormat(&clock);
	PrintLog(0, "ϵͳ����ʱ��: %s\n", pstr);

	
	PrintLog(0, "  �ն�IP��ַ: %d.%d.%d.%d\n",
			ParaUniG.termip.ipterm[0], ParaUniG.termip.ipterm[1], 
			ParaUniG.termip.ipterm[2], ParaUniG.termip.ipterm[3]);
	PrintLog(0, " �ն�MAC��ַ: %02X:%02X:%02X:%02X:%02X:%02X\n", 
			ParaUniG.addr_mac[0], ParaUniG.addr_mac[1], ParaUniG.addr_mac[2], 
			ParaUniG.addr_mac[3], ParaUniG.addr_mac[4], ParaUniG.addr_mac[5]);
	PrintLog(0, "  �����˿ں�: %d\n", ParaUniG.termip.portlisten);
	PrintLog(0, " �� �� �� ��: %s\n", ParaUniG.manuno);
	PrintLog(0, "�ڲ��������: %s\n", ParaUniG.manuno_inner);

	PrintLog(0, "��վIP %d.%d.%d.%d:%d\n", 
			    ParaTermG.svraddr.net.ip[0], ParaTermG.svraddr.net.ip[1],
			    ParaTermG.svraddr.net.ip[2], ParaTermG.svraddr.net.ip[3],
			    ParaTermG.svraddr.net.port);		

	return 0;
}
DECLARE_SHELL_CMD("info", shell_sysinfo, "��ӡϵͳ��Ϣ");


extern void BcdToHex(unsigned char *str, int len);

