/**
* operation.c -- ����ģ���ʼ��
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-8
* ����޸�ʱ��: 2009-5-8
*/

#include <stdio.h>

#include "include/debug.h"
#include "include/param/term.h"
#include "include/param/sceneuse.h"
#include "include/sys/schedule.h"
#include "operation_inner.h"
#include "include/environment.h"
extern int ParamSaveInit(void);
/**
* @brief ����ģ���ʼ��
* @return 0�ɹ�, ����ʧ��
*/
DECLARE_INIT_FUNC(ParamInit);
int ParamInit(void)
{
	PrintLog(0,"load param ...\n");
	PrintLog(0,"  LoadParaUni ...\n");
	LoadParaUni();//���Զ������
	PrintLog(0,"  LoadParaTerm ...\n");
	LoadParaTerm(); //���ļ��е��ն� ���ò�����Ϣ 
//	LoadParaDataUse();	//��ȡ�龰�б�
//	LoadParaTimerTask();//��ȡ��ʱ����
	
	Sleep(500);
	if(ParamSaveInit()) return 1;
	SET_INIT_FLAG(ParamInit);	
	return 0;
}


