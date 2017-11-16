/**
* plccomm.c -- �ز�ͨ�Žӿ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-21
* ����޸�ʱ��: 2009-5-21
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define DEFINE_PLCOMM

#include "include/basetype.h"
#include "include/debug.h"
#include "include/sys/schedule.h"
#include "include/sys/mutex.h"
#include "include/sys/uart.h"
#include "include/sys/timeal.h"
#include "include/sys/timer.h"
#include "include/sys/gpio.h"
#include "include/lib/crc.h"
#include "include/lib/align.h"
#include "include/param/unique.h"
#include "include/param/term.h"
#include "include/param/commport.h"
#include "include/param/operation.h"
#include "plcomm.h"
#include "downlink/module/rfmet.h"
#include "include/debug/shellcmd.h"

#include "save/param.h"

static sys_mutex_t PlcMutex;
//static int RouteWriteErrCount = 0;
//static int UpdNodeErrCount = 0;//ͬ���ӵ�ʧ�ܴ���
#define PLC_LOCK	SysLockMutex(&PlcMutex)
#define PLC_UNLOCK	SysUnlockMutex(&PlcMutex)
#define PLXCBUFFER_MAXLEN	256

int PlcMetRegisting = 0;//���ڹ㲥��ȡ���(����Զ�ע��)
int PlcMetRegistStart = 0;
int PlcMetReading = 0;	// 1Ϊ ���ڽ��е㳭


int PlcSamplingMetid = -1;
static unsigned char PlCommBuffer[PLCOMM_BUF_LEN];
unsigned char PlXcBuffer[PLXCBUFFER_MAXLEN];



/**
* @brief ���ͨ�Ż�����ָ��
*/
unsigned char *GetPlCommBuffer(void)
{
	return PlCommBuffer;
}

struct plc_module {
	unsigned char devno;
	int (*read)(const plc_dest_t *dest, unsigned long itemid, unsigned char *buf, int len);
	int (*ctrlmet)(const plc_dest_t *dest, unsigned long itemid,unsigned char *buf, int len);
	const char* moduleName;
};
static const struct plc_module PlcModules[] = {
	{1, RFMetRead,RFMetCtrl,"ModBus"},
};
#define NUM_MODULES		(sizeof(PlcModules)/sizeof(PlcModules[0]))
int PlcModuleNo = 0;        		


/*
* @brief ����ӿڣ�����������
*/
int GetPlcModeuleNo(void)
{
	return PlcModuleNo;
}

/*
* @brief ����ӿڣ�������������
*/
void SetPlcModeuleNo(const int type)
{
	
	if(type >= NUM_MODULES || type < 0) {//???
		PlcModuleNo = 0;
	}
	
	PlcModuleNo = type;
	ParaUniG.downlink = type;
	SetSaveParamFlag(SAVFLAG_PARAUNI);
	SaveParam();
}


/*
*@brief ��ȡ�ز���������
*
*/
void GetModulesName(char *pbuff,int nLen)
{
	strncpy(pbuff,PlcModules[PlcModuleNo].moduleName,nLen);
}

/**
* @brief ����Ŀ���ַ
* @param metid Ŀ�ı��
* @param dest ����Ŀ���ַ����ָ��
*/
void MakePlcDest(unsigned short metid, plc_dest_t *dest)
{
	int i;
	dest->metid = metid;

	dest->portcfg = 1;
}

/**
* @brief ������
* @param dest Ŀ�ĵ�ַ
* @param itemid �������ʶ
* @param buf ����֡������ָ��
* @param len ����������
* @return �ɹ�����ʵ�����ݳ���, ʧ�ܷ���-1
*/
int PlcRead(const plc_dest_t *dest, unsigned long itemid, unsigned char *buf, int len)
{
	int rtn;

	if( PlcMetRegisting) return -1;
	PlcMetReading = 1;
	DebugPrint(0,"read....plcModuleNo=%d\r\n",PlcModuleNo);
	PLC_LOCK;
	if(NULL == PlcModules[PlcModuleNo].read) {
		PLC_UNLOCK;
		return -1;
	}
	rtn = (*PlcModules[PlcModuleNo].read)(dest, itemid, buf, len);
	PLC_UNLOCK;
	PlcMetReading = 0;
	return rtn;
}


/**
* @brief ��������բ
* @param dest Ŀ�ĵ�ַ
* @param pconfig д����
* @param buf ����֡������ָ��
* @param len ����������
* @return �ɹ�����0, ����ʧ��
*/
int PlcCtrlMet(const plc_dest_t *dest, unsigned long itemid,unsigned char *buf,int len)
{
	int rtn;
	PrintLog(0, "In PlcCtrlMet...\n");
	PrintLog(0, "PlcModuleNo = %d\n", PlcModuleNo);
//	if( PlcMetRegisting) return -1;
	PlcMetReading = 1;
	PLC_LOCK;
	if(NULL == PlcModules[PlcModuleNo].ctrlmet) {
		PLC_UNLOCK;
		return -1;
	}
	rtn = (*PlcModules[PlcModuleNo].ctrlmet)(dest, itemid,buf,len);
	PLC_UNLOCK;
	PlcMetReading = 0;
       DebugPrint(0, "rtn len (%d):\n", rtn);
	return rtn;
}

/*
* @brief �ز�ͨ�ų�ʼ������
* @return ����0��ʾ�ɹ�, ����ʧ��
*/
DECLARE_INIT_FUNC(PlcCommInit);
int PlcCommInit(void)
{
	PrintLog(0,"  plccomm init..\n");

	SysInitMutex(&PlcMutex);
	
	SET_INIT_FLAG(PlcCommInit);

	return 0;
}

