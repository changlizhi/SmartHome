/**
* msgproc.c -- ����ͨ�������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-18
* ����޸�ʱ��: 2009-5-18
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "include/basetype.h"
#include "include/version.h"
#include "include/debug.h"
#include "include/sys/schedule.h"
#include "include/sys/reset.h"
#include "include/sys/mutex.h"
#include "include/sys/timeal.h"
#include "include/sys/timer.h"
#include "include/sys/bin.h"
#include "include/sys/syslock.h"
#include "include/sys/gpio.h"
#include "include/lib/bcd.h"
#include "include/lib/dbtime.h"
#include "include/lib/align.h"
#include "include/lib/datachg.h"
#include "save/param.h"
#include "include/param/term.h"
#include "include/param/capconf.h"
#include "include/param/unique.h"

#include "include/debug/svrcomm_shell.h"
#include "uplink_pkt.h"
#include "uplink_dl.h"
#include "svrcomm.h"
#include "downlink/plcomm.h"
#include "downlink/plmdb.h"

#include "include/param/sceneuse.h"

static unsigned char recv_othebuf[512];/*�����еڶ������պ������ͻ���*/

unsigned short SceneMask = 0;//ĳλΪ1��ʾ��λ������龰��ſ���
						//�����ڿ���ĳ���龰
unsigned char SceneOnId = 0;//������ǰ�龰
unsigned char SceneOffId = 0;//�رյ�ǰ�龰

unsigned char DevMask[MAX_METER+1] = {0};//Ϊ1��ʾд�豸״̬�ɹ�
extern int plcreading;									//Ϊ0��ʾʧ��

unsigned char	 LedStr[512]={0};
unsigned char  	 UpdateLedFlag = 0; //UpdateLedFlagΪ1��ʾ��Ҫ�������ݵ���ʾ����Ϊ0��ʾ���ø�������

unsigned char	 audiourl[512]={0};			//�������·�����Ƶ�ļ����ص�ַ
unsigned char  	 UpdateAudiourlFlag = 0;	//������Ƶ�ļ���־��0��ʾδ����Ƶ��������1��ʾ����Ƶ��������

unsigned char  	 DeviceCheckResultFlag = 0;	//���������ص��豸��֤�����0X18������Ƶ�������ţ�0X1FΪ��Ƶ����ǿ����ֹ��


#define MET_ONOFF_NUM sizeof(met_onoff)/sizeof(met_onoff[0])

/*
// д�豸����
*/
static int svr_login_terminal(int itf)
{
	faalpkt_t *precv = (faalpkt_t *)FAAL_RCVBUF(itf);
	faalpkt_t *psend = (faalpkt_t *)FAAL_SNDBUF(itf);
	unsigned char * pu = precv->data;

//	int rtn;

	psend->cmd = FAALCMD_ECHO_LOGIN;

	if(memcmp(pu+32,ParaUniG.termip.pwd,32)==0)
	{		
		FAAL_SETLEN(psend, 1);
		psend->data[0] = FAALERR_OK;
		faal_sendpkt(itf, psend);
	}
	else
	{
		FAAL_SETLEN(psend, 1);
		psend->data[0] = FAALERR_PWERR;
		faal_sendpkt(itf, psend);
	}

	return 0;
}
static int svr_heart_beat(int itf)
{
	faalpkt_t *precv = (faalpkt_t *)FAAL_RCVBUF(itf);
	faalpkt_t *psend = (faalpkt_t *)FAAL_SNDBUF(itf);
	unsigned char * pu = precv->data;
	psend->cmd = FAALCMD_ECHO_HEARTBEAT;
	FAAL_SETLEN(psend, 0);
	faal_sendpkt(itf, psend);
	return 0;
}

extern void ClearSaveParamFlag(void);
extern void SaveParam(void);



//#ifdef DEBUGMODE
//#define MAX_PKTLEN 40//400
//#else
#define MAX_PKTLEN (UPLINK_SNDMAX(itf)-100)
//#endif


extern int UplinkRecvPkt(unsigned char itf);


#define MAX_FRAME 7



static sys_mutex_t QueryCacheMutex;

//��վ�·���Ƶ�ļ���������
static int svr_update_audio_url(int itf)
{
	faalpkt_t *precv = (faalpkt_t *)FAAL_RCVBUF(itf);
	unsigned short datalen = makepkt_short(precv->len);//���ݳ���
	memcpy(audiourl,precv->data,datalen);
	UpdateAudiourlFlag = 1;
	PrintLog(0,"audio usl is :%s",audiourl);
	
	return 1;

}

//��վ���豸��У��ظ��������
static int svr_device_check_result(int itf)
{
	faalpkt_t *precv = (faalpkt_t *)FAAL_RCVBUF(itf);
	unsigned short datalen = makepkt_short(precv->len);//���ݳ���
	DeviceCheckResultFlag = precv->data[0];
	if(DeviceCheckResultFlag == 0x18)
	   PrintLog(0,"audio is  Continue Play :%02x\n",DeviceCheckResultFlag);
	else if(DeviceCheckResultFlag == 0x1F)
	   PrintLog(0,"audio is  Stop Play :%02x\n",DeviceCheckResultFlag);
	return 0;

}



typedef int (*msgproc_pf)(int itf);
typedef struct {
	unsigned char cmd;
	msgproc_pf pf;
} svrmsg_func_t;

const svrmsg_func_t g_srvmsg_flist[] = {
	{FAALCMD_LOGIN, svr_login_terminal},
	{FAALCMD_HEARTBEAT,svr_heart_beat},
	{FAALCMD_UPDATEAUDIOSTR, svr_update_audio_url},
	{FAALCMD_DEVICECHECK, svr_device_check_result},
		
	{0xff, NULL},
};

extern void faal_printpkt(faalpkt_t *pkt, char *prompt);
void SvrMessageProc(unsigned char itf)
{ 
	faalpkt_t *precv = (faalpkt_t *)FAAL_RCVBUF(itf);
	faalpkt_t *psend = (faalpkt_t *)FAAL_SNDBUF(itf);
	int rtn;
	unsigned char cmd;
	const svrmsg_func_t *plist = g_srvmsg_flist;
	PrintLog(0,"SvrMessageProc:%02x\n",precv->head);
	PrintLog(0,"SvrMessageProcdep:%02x\n",precv->dep);
	PrintLog(0,"SvrMessageProc:%02x\n",precv->cmd);
	PrintHexLog(0,&precv->head,30);

	PrintLog(0,"SvrMessageProc:%02x",precv->cmd);

    psend->cmd = precv->cmd;
		
	rtn = (int)makepkt_short(precv->len);
	rtn &= 0xffff;
	rtn += LEN_FAAL_HEAD;
	if(rtn > FAAL_RCVMAX(itf)) return;

	cmd = (precv->cmd)&FAALMASK_CMD;
	while(0xff != plist->cmd)
	{
		PrintLog(0,"plist->cmd:%02x,cmd:%02x\n",plist->cmd,cmd);
		if(cmd == plist->cmd)
		{
			if(*plist->pf == NULL)
				return;
			rtn = (*plist->pf)(itf);
			PrintLog(0,"rtn:%d\n",rtn);
			if(rtn)
			{
				psend->len[0] = 0;
				psend->len[1] = 0;
				psend->cmd |= FAALMASK_DIR;
				faal_sendpkt(itf, psend);
			}
			
			return;
		}

		plist++;
	}

}
/**
* @brief ��Ϣ����ģ���ʼ��
*/
DECLARE_INIT_FUNC(SvrMessgeInit);
int SvrMessgeInit(void)
{
	SysInitMutex(&QueryCacheMutex);

	SET_INIT_FLAG(SvrMessgeInit);
	return 0;
}
