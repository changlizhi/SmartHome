/**
* driver_init.c -- ������ʼ������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-4-24
* ����޸�ʱ��: 2009-5-6
*/

#include <stdio.h>
#include "include/debug.h"

extern int GpioInit(void);

/**
* @brief �����ӿ���ģ���ʼ������(�߼�����)
* @return 0�ɹ�, ����ʧ��
*/
DECLARE_INIT_FUNC(DriverHighInit);
int DriverHighInit(void)
{
	if(GpioInit()) return 1;
	SET_INIT_FLAG(DriverHighInit);
	return 0;
}
