/**
* mdb.c -- ���ģ���ʼ��
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-15
* ����޸�ʱ��: 2009-5-15
*/

#include <stdio.h>

#include "include/debug.h"

extern int MonitorTaskInit(void);

/**
* @brief ���ģ���ʼ��
* @return �ɹ�0, ����ʧ��
*/
DECLARE_INIT_FUNC(MonitorInit);
int MonitorInit(void)
{
	PrintLog(0,"monitor init...\n");
	MonitorTaskInit();

	SET_INIT_FLAG(MonitorInit);
	return 0;
}
