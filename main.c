/**
* main.c -- Ӧ��������������
* 
* ����: csg
* ����ʱ��: 2012-5-4
* ����޸�ʱ��: 2012-5-4
*/
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "include/basetype.h"
#include "include/debug.h"
#include "include/startarg.h"
#include "include/sys/init.h"
#include "include/version.h"
#include "include/sys/task.h"
#include "include/sys/schedule.h"
#include "include/sys/timeal.h"
#include "include/sys/timer.h"
#include "include/sys/gpio.h"
#include "include/param/term.h"
#ifdef OPEN_DEBUGPRINT
static const char VersionDebugInfo[] = "debug";
#else
#ifdef OPEN_ASSERTLOG
static const char VersionDebugInfo[] = "test";
#else
static const char VersionDebugInfo[] = "release";
#endif
#endif

int   exitflag = 0;
/**
* @brief ��������
*/
static void startup(void)
{

	if(SysInit())
	{
		return;
	}

	if(DebugInit())
	{
		return;
	}
	if(ParamInit())
	{
		return;
	}
	MonitorInit();

	
	SvrCommInit();
	CheckInitFlag();
	{
		sysclock_t clock;

		if(SysClockRead(&clock)) PrintLog(0,"read system clock failed.\n");
		else PrintLog(0,"current time = %s\n", SysClockFormat(&clock));
	}
	
	SysWaitTaskEnd();

}
/**
* ��������:
* '-b': ��̨����
* '-s': ���������н���
* '-d': ��ι��, ������
* '-rXXX': ttyʹ��rawģʽ, XXXΪ���ڲ�����
* '-pXXX': ttyʹ��rawģʽ,�����������ڽ�������, XXXΪ���ڲ�����
*          -b, -s, -r , -p ����ͬʱ��Ч
*/

static void ParseArgs(int argc, char *argv[])
{
	int i;

	for(i=1; i<argc; i++) {
		if('-' != argv[i][0] || 0 == argv[i][1]) continue;

		SetStartArg(argv[i]+1);
	}
}



/**
* @brief ���������
* @param argc ������Ŀ
* @param argv �����б�
* @return 0��ʾ�ɹ�, ����ʧ��
*/
int main(int argc, char *argv[])
{
	printf("\n\n");
	printf("\033[1;32m" "����XX��˾\n");
	printf("Relase Date: 20%02d-%d-%d %d:%d %s \033[0m\n\n", 
		_mk_year, _mk_month, _mk_day, _mk_hour, _mk_minute, VersionDebugInfo);

	ParseArgs(argc, argv);
	if(MakeDeviceCode() !=0)//��������豸��ַ.
	{
		printf("Ӧ�ó���Ƿ�,����ʧ��\n\n");
		return 0; 
	}

	if(!GetStartArg('b', NULL, 0))//��̨����
	{ 
		if(fork() == 0) 
		{
			startup();
		}
	}
	else //�Ǻ�̨����
	{
		startup();
	}
	return 0;
}
