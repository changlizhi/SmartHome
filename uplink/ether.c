/**
* ether.c -- ��̫��ͨ��(�ͻ���ģʽ)
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-19
* ����޸�ʱ��: 2009-5-19
*/

#include <stdio.h>
#include <string.h>
#include <ctype.h>

#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <fcntl.h>
#include <arpa/inet.h>
#include <sys/errno.h>
#include <sys/ioctl.h>

#include "include/basetype.h"
#include "include/debug.h"
#include "include/sys/schedule.h"
#include "include/sys/gpio.h"
#include "include/lib/align.h"
#include "include/param/term.h"
#include "include/uplink/svrnote.h"

#include "uplink_pkt.h"
#include "uplink_dl.h"
#include "svrcomm.h"
#include "keepalive.h"

static int SockEther = -1;

#define CLOSE_SOCKET(sock)   { \
	if((sock) >= 0) { \
		close(sock); \
		sock = -1; \
	}}

extern void GpioSetValue(unsigned char io, int value);

/**
* @brief ���ӵ�������
* @return �ɹ�0, ����ʧ��
*/
static int EtherConnect(void)
{
	static int ServerSel = 0;//��վ�����л����(Ĭ����������վ��ַ)
	static int CountFail = 0;
	
	struct sockaddr_in addr;
	unsigned long ip;
	unsigned short port;
	//int ctlflag;

	CLOSE_SOCKET(SockEther);
       int proto = 0;//Ĭ��ΪTCP��ʽ
	if(proto) //UDP
	{	SockEther = socket(AF_INET, SOCK_DGRAM, 0);
		SockEther = socket(AF_INET, SOCK_DGRAM, 0);
	}
	else  //TCP
	{
		SockEther = socket(AF_INET, SOCK_STREAM, 0);
		SockEther = socket(AF_INET, SOCK_STREAM, 0);
	}
	if(SockEther < 0) {
		PrintLog(LOGTYPE_ALARM, "create socket errror.\n");
		return 1;
	}
	
	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	
       if(0 == ServerSel)
       {
          	port = ParaTermG.svraddr.net.port;
          	addr.sin_port = htons(port);
	   	ip = addr.sin_addr.s_addr = MAKE_LONG(ParaTermG.svraddr.net.ip);
       }
	else
       {
          	port = ParaTermG.svraddr_1.net.port;
          	addr.sin_port = htons(port);
	   	ip = addr.sin_addr.s_addr =MAKE_LONG( ParaTermG.svraddr_1.net.ip);
       }
	 PrintLog(0,"connect to %d.%d.%d.%d, %d...\n",
			ip&0xff, (ip>>8)&0xff, (ip>>16)&0xff, (ip>>24)&0xff, port);  
	PrintLog(LOGTYPE_SHORT, "connect to %d.%d.%d.%d, %d...\n",
			ip&0xff, (ip>>8)&0xff, (ip>>16)&0xff, (ip>>24)&0xff, port);

	if(connect(SockEther, (struct sockaddr *)&addr, sizeof(addr)) == 0) {
		PrintLog(0, "connect succeed.\r\n");
		
		//CountFail = 0;
		return 0;
	}
	DebugPrint(0, "connect failed.\n");
	PrintLog(0, "connect failed.\n");
	CLOSE_SOCKET(SockEther);

	/*by ydl add 2011-05-04*/
	CountFail++;

	if(CountFail == 2) {
		system("wifi down");
	}

	return 1;
}

/**
* @brief ��������Ͽ�����
* @return �ɹ�0, ����ʧ��
*/
static int EtherDisconnect(void)
{
	CLOSE_SOCKET(SockEther);
	return 0;
}

/**
* @brief ��½������
* @return �ɹ�0, ����ʧ��
*/
static int EtherLogon(void)
{
	SetKeepAlive(KEEPALIVE_FLAG_LOGONFAIL);

	SvrCommLineState = LINESTAT_OFF;

	
	if(UplinkLogon(UPLINKITF_ETHER)) 
	{     
		EtherDisconnect();
		return 1;
	}
       //���ߡ����� ֻ�з��͵�¼���ҽӵ���Ӧ�������ΪON
    PrintLog(0,"��¼�ɹ�!\n");
	ParaTermG.login_update_system = 1;
	ParaTermG.login_down_musice	= 1;
//	UplinkLogonOut(UPLINKITF_ETHER);   
	UplinkDeviceCheck(UPLINKITF_ETHER);
	
	Sleep(1000);//
	
	UplinkCheckVer(UPLINKITF_ETHER);
	Sleep(2000);
	SvrCommLineState = LINESTAT_ON;
	SetKeepAlive(KEEPALIVE_FLAG_LOGONOK);
	SvrCommNote(SVRNOTEID_ALARM);
	
	return 0;
}

/**
* @brief �����������������
* @return �ɹ�0, ����ʧ��
*/
static int EtherKeepAlive(void)
{
	int rtn = 0;

	PrintLog(LOGTYPE_SHORT, "ether keep alive...\n");

	if(LINESTAT_ON == SvrCommLineState) 
	{     
		//��·���ã����ж��Ƿ���Ҫ��������
		rtn = UplinkLinkTest(UPLINKITF_ETHER);
		//������·���󣬲��ܳɹ����ֱ����0
		//����������ݳ�ʱ���Ƿ���Ҫ������·?
		if((UPRTN_FAIL == rtn) || (UPRTN_TIMEOUT == rtn)) 
		{
			SvrCommLineState = LINESTAT_OFF;
			
			EtherDisconnect();
			gpio_set_value(GPIO_LED_NET,0);
		}
		else if(UPRTN_OK == rtn) 
		{
			/*by ydl add 2011-05-04*/
			ClearKeepAlive();
			/*end*/
			return 0;
		}
		else 
		{    	//�յ���վ�·���֡������(�ǻ�Ӧ֡)
		    	//   keepalive_stat.cnt = 0;//��0
			SvrMessageProc(UPLINKITF_ETHER);//test
			return 0;
		}
	}
       //��·���õ�ʱ�򲻽�������
	if(!EtherConnect())
	{
		Sleep(50);
		return(EtherLogon()); //���͵�¼֡
	}
	
       //�������ʧ�ܣ���ر�SOCKET��
	EtherDisconnect();
	SvrCommLineState = LINESTAT_OFF;
	return 1;
}

/**
* @brief ��̫��ͨ������
*/
void EtherTask(void)
{
	unsigned long ev;

	UplinkClearState(UPLINKITF_ETHER);
	SvrCommLineState = LINESTAT_OFF; //�ر�״̬
  //    while(0 == (ParaTermG.cascade_flag&0x01) )
	 Sleep(20);//����ǴӼ�������������̫������
	EtherKeepAlive();

	while(1) 
	{

		SvrCommPeekEvent(SVREV_NOTE, &ev); 
		if(ev&SVREV_NOTE) 
		{
			if(!RefreshKeepAlive()) EtherKeepAlive();
			if(LINESTAT_ON == SvrCommLineState) SvrNoteProc(UPLINKITF_ETHER);
		}
              /*��� ��̫�� ������*/
		if(LINESTAT_ON == SvrCommLineState) 
		{

			//���յ����������͹���������
			if(!UplinkRecvPkt(UPLINKITF_ETHER)) 
			{
				PrintLog(0,"SvrMessageProc: " );
				
				Sleep(10);
				//������������͹���������
				SvrMessageProc(UPLINKITF_ETHER);				
			}
		}

		if(!KeepAliveProc()) EtherKeepAlive();
		if(exitflag)
		{
			EtherDisconnect();
			break;
		}
		Sleep(10);
	}
}

static unsigned char ether_recvbuf[2048];
static int ether_recvlen = 0;
static int ether_recvhead = 0;
/**
* @brief ����̫��ͨ�Žӿڶ�ȡһ���ֽ�
* @param buf �����ַ�ָ��
* @return �ɹ�0, ����ʧ��
*/

unsigned char StrToHex(unsigned char *psrc1, unsigned char *psrc2)
{
	char h1,h2;
	unsigned char ret=0;
	unsigned char s1,s2;
	int i;
	h1 = psrc1;
	h2 = psrc2;

	s1 = toupper(h1) - 0x30;
	if (s1 > 9) 
	  s1 -= 7;

	s2 = toupper(h2) - 0x30;
	if (s2 > 9) 
		s2 -= 7;
	ret = s1*16 + s2;
	return ret;
}

int EtherGetChar(unsigned char *buf)
{
	if(SockEther < 0) return 1;

	if(ether_recvlen <= 0) 
	{
		//ether_recvlen = recv(sock_ether, ether_recvbuf, 2048, 0);
		ether_recvlen = recv(SockEther, ether_recvbuf, 2048, MSG_DONTWAIT);
//		PrintLog(0,"ether_recvlen=%d,errno=%d",ether_recvlen,errno);
		if(((ether_recvlen < 0) && (errno != EWOULDBLOCK)) ||
				(ether_recvlen == 0)) {
			PrintLog(LOGTYPE_SHORT, "connection corrupted(%d,%d).\n", ether_recvlen, errno);
			CLOSE_SOCKET(SockEther);
			SvrCommLineState = LINESTAT_OFF;
			return 1;
		}
		else if(ether_recvlen < 0) {
			return 1;
		}
		else {
			ether_recvhead = 0;
		}
	}

	*buf = ether_recvbuf[ether_recvhead++];
	ether_recvlen--;
	return 0;
}
int  HexToStr(unsigned char *pbDest, unsigned char *pbSrc, int nLen)
{
	char	ddl,ddh;
	int i;

	for (i=0; i<nLen; i++)
	{
		ddh = 48 + pbSrc[i] / 16;
		ddl = 48 + pbSrc[i] % 16;
		if (ddh > 57) ddh = ddh + 7;
		if (ddl > 57) ddl = ddl + 7;
		pbDest[i*2] = ddh;
		pbDest[i*2+1] = ddl;
	}

	pbDest[nLen*2] = '\0';
	return nLen*2+1;
}

/**
* @brief ����̫��ͨ�Žӿڷ�������
* @param buf ���ͻ�����ָ��
* @param len ����������
* @return �ɹ�0, ����ʧ��
*/
int EtherRawSend(const unsigned char *buf, int len)
{
	//int i, buflen;

	if(SockEther < 0) return 1;
	unsigned char senddata[1024] = {0};
	if(send(SockEther, buf, len, MSG_NOSIGNAL) < 0) {
		DebugPrint(1, "send fail\r\n");
		goto mark_failend;
	}

	return 0;

#if 0
	//wait until send buffer empty
	for(i=0; i<100; i++) {
		osh_sleep(10);

		if(ioctl(sock_ether, SIOCOUTQ, &buflen)) goto mark_failend;

		//debug_print(1, "buflen = %d\r\n", buflen);
		if(0 == buflen) return 0;
	}
#endif

mark_failend:
	PrintLog(LOGTYPE_SHORT, "connection corrupted.\r\n");
	PrintLog(0,"\n connect courrupted. \n");
	CLOSE_SOCKET(SockEther);
	SvrCommLineState = LINESTAT_OFF;
	return 1;
}
