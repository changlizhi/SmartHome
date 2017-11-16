/**
* plccomm.h -- �ز�ͨ�Žӿ�ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-4-24
* ����޸�ʱ��: 2009-4-24
*/

#ifndef _PLCOMM_H
#define _PLCOMM_H

//Ŀ������
typedef struct {
	unsigned short metid;  // ��1��ʼ, 0��Ч
	unsigned char portcfg;// 1-RS232, 2-��̫��
	unsigned char proto;
} plc_dest_t;


#define PLCOMM_BUF_LEN		272
unsigned char *GetPlCommBuffer(void);

void MakePlcDest(unsigned short metid, plc_dest_t *dest);

#define PLCHKTIME_POLL		1   //��ѯ��ʽ�ϱ�
#define PLCHKTIME_BROCAST	2   //�㲥��ʽ�ϱ�

//���ش�����
#define PLCERR_INVALID		-1
#define PLCERR_TIMEOUT		-2

int PlcRead(const plc_dest_t *dest, unsigned long itemid, unsigned char *buf, int len);
int PlcCtrlMet(const plc_dest_t *dest, unsigned long itemid,unsigned char *buf,int len);
void GetModulesName(char *pbuff,int nLen);
void SetPlcModeuleNo(const int type);
int GetPlcModeuleNo(void);

#ifndef DEFINE_PLCOMM
//extern const int PlcTimeChecking;
extern int PlcMetRegistStart;
extern unsigned char PlXcBuffer[256];

extern int PlcSamplingMetid ;
#endif

#endif /*_PLCOMM_H*/

