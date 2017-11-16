/**
* syslock.c -- ϵͳ��Դ���ӿں���
* ��ĳЩ����ǰ��Ҫ��ֹ�ļ�����, �����
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-5
* ����޸�ʱ��: 2009-5-5
*/

#include "include/debug.h"
#include "include/sys/mutex.h"
#include "sys/sys_config.h"

static int SysLockNum = 0;
static sys_mutex_t SysLock[MAX_SYSLOCK];

/**
* @brief ע��һ��ϵͳ��Դ��
* @return �ɹ�������Դ��id, ���򷵻�-1
*/
int RegisterSysLock(void)
{
	int i;

	AssertLogReturn(SysLockNum>=MAX_SYSLOCK, -1, "syslock too much\n");

	i = SysLockNum;
	SysInitMutex(&SysLock[i]);
	SysLockNum++;

	return(i);
}

/**
* @brief ��סһ��ϵͳ��Դ��
* @param id ϵͳ��Դ��id
*/
void LockSysLock(int id)
{
	if((id < 0) || (id >= SysLockNum)) {
		ErrorLog("invalid id(%d)\n", id);
		return;
	}

	SysLockMutex(&SysLock[id]);
}

/**
* @brief ����һ��ϵͳ��Դ��
* @param id ϵͳ��Դ��id
*/
void UnlockSysLock(int id)
{
	if((id < 0) || (id >= SysLockNum)) {
		ErrorLog("invalid id(%d)\n", id);
		return;
	}

	SysUnlockMutex(&SysLock[id]);
}

/**
* @brief ��ֹ����ע����ϵͳ��Դ���Ĳ���
*/
void SysLockHalt(void)
{
	int i;

	for(i=0; i<SysLockNum; i++) {
		SysLockMutex(&SysLock[i]);
	}
}

