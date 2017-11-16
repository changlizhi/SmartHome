/**
* operation.c -- ��������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-7
* ����޸�ʱ��: 2009-5-8
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "param_config.h"
#include "include/debug.h"
#include "include/sys/syslock.h"
#include "include/param/capconf.h"
#include "include/param/operation.h"
#include "include/param/unique.h"
#include "include/param/sceneuse.h"
#include "include/debug/shellcmd.h"
#include "save/param.h"
#include "operation_inner.h"

static int ParamSaveSysLock = -1;
/**
* @brief ��ʼ����������
* @return 0�ɹ�, ����ʧ��
*/
DECLARE_INIT_FUNC(ParamSaveInit);
int ParamSaveInit(void)
{
	PrintLog(0,"  param save init..\n");

	ParamSaveSysLock = RegisterSysLock();
	if(ParamSaveSysLock < 0) {
		ErrorLog("register syslock fail\n");
		return 1;
	}
	
	SET_INIT_FLAG(ParamSaveInit);

	return 0;
}

static unsigned int SaveFlag = 0;

/**
* @brief ������������־
*/
void ClearSaveParamFlag(void)
{
	SaveFlag = 0;
}

/**
* @brief ���ò��������־
* @param flag ��־λ
*/
void SetSaveParamFlag(unsigned int flag)
{
	SaveFlag |= flag;
}


typedef int (*savefunc_t)(void);
static const savefunc_t FunctionSave[FILEINDEX_MAX] = {
	SaveParaTerm, SaveParaUni, SaveParaSceneUse,SaveParaTimerTask,
};

/**
* @brief �������
*/
void SaveParam(void)
{
	int index;
	unsigned int mask;

	LockSysLock(ParamSaveSysLock);

	for(index=0,mask=1; index<FILEINDEX_MAX; index++,mask<<=1) 
	{
		if(mask&SaveFlag) 
		{	
			DebugPrint(0, "save index:%d\n", index);
			(*FunctionSave[index])();
		}
	}

	UnlockSysLock(ParamSaveSysLock);

	SaveFlag = 0;
}


