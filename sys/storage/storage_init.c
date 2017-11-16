/**
* storage.c -- ϵͳ����ģ���ʼ������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-5
* ����޸�ʱ��: 2009-5-5
*/

#include <stdio.h>

#include "include/debug.h"

extern int XinInit(void);
extern int FlatInit(void);

/**
* @brief ϵͳ����ģ���ʼ������
* @return ����0��ʾ�ɹ�, ����ʧ��
*/
DECLARE_INIT_FUNC(StorageInit);
int StorageInit(void)
{

	if(XinInit()) return 1;
	if(FlatInit()) return 1;

	SET_INIT_FLAG(StorageInit);

	return 0;
}

