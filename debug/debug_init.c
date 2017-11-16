/**
* debug_init.c -- ����ģ���ʼ��
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-26
* ����޸�ʱ��: 2009-5-26
*/

#include <stdio.h>
#include "include/debug.h"
#include "include/startarg.h"

extern int EthShellInit(void);
extern int ShellCmdInit(void);
extern int TtyShellStart(void);
extern int PipeShellInit(void);
extern int LoadDebugStatistics(void);
extern int SvrShellInit(void);

DECLARE_INIT_FUNC(DebugInit);
int DebugInit(void)
{

	ShellCmdInit();

	if(EthShellInit()) return 1;
//	if(PipeShellInit()) return 1;
		                                       

	if(GetStartArg('b', NULL, 0)) { //ǰ̨����
		if(!GetStartArg('s', NULL, 0)) { //���������н���
			TtyShellStart();
		}
	}

	LoadDebugStatistics();

	SET_INIT_FLAG(DebugInit);
	return 0;
}

