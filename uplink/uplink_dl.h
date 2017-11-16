/**
* uplink_dl.h -- ����ͨ��������·��
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-18
* ����޸�ʱ��: 2009-5-18
*/

#ifndef _UPLINK_DL_H
#define _UPLINK_DL_H

#ifndef _FAAL_H
#include "svrcomm/faal.h"
#endif
#ifndef _FAAL_DL_H
#include "svrcomm/faal_dl.h"
#endif


//����ͨ���ŵ����

#define UPLINKITF_SERIAL		0   //����
#define UPLINKITF_ETHMTN		1   //��̫��������
#define UPLINKITF_ETHER			2  //��̫��
#define UPLINKITF_TCPSVR          	3
#define UPLINKITF_LOCALSVR         4

#define UPLINKITF_NUM			5

#define UPLINKATTR_NOECHO    0x01    //�������Ͳ�����Ӧ(������ŵ�)

#define UPLINK_NEEDPRINT(itf)   (((itf) >=UPLINKITF_ETHMTN) && (LOGITF_SVRCOMM != GetLogInterface()))

typedef struct {
	unsigned char *rcvbuf;  //���ջ���
	unsigned char *sndbuf;    //���ͻ���
	int (*rawsend)(const unsigned char *buf, int len);    //���ͺ���
	int (*getchar)(unsigned char *buf);    //���պ���
	int (*linestat)(void);
	int timeout;   //���ճ�ʱ

	int rcvmax;    //������������󳤶�
	int sndmax;    //������������󳤶�
	int sndnor;     //��������һ�㳤������

	unsigned int attr;   //ͨ������
} uplinkitf_t;

extern const uplinkitf_t UplinkInterface[UPLINKITF_NUM];
#define UPLINK_RCVBUF(itf)		(UplinkInterface[itf].rcvbuf)
#define UPLINK_SNDBUF(itf)		(UplinkInterface[itf].sndbuf)
#define UPLINK_RCVMAX(itf)		(UplinkInterface[itf].rcvmax)
#define UPLINK_TIMEOUT(itf)		(UplinkInterface[itf].timeout)
#define UPLINK_SNDMAX(itf)		(UplinkInterface[itf].sndmax)
#define UPLINK_SNDNOR(itf)		(UplinkInterface[itf].sndnor)
#define UPLINK_ATTR(itf)			(UplinkInterface[itf].attr)

#define FAAL_RCVBUF(itf)   (UplinkInterface[itf].rcvbuf)
#define FAAL_SNDBUF(itf)    (UplinkInterface[itf].sndbuf)
#define FAAL_RCVMAX(itf)   (UplinkInterface[itf].rcvmax)
#define FAAL_TIMEOUT(itf)    (UplinkInterface[itf].timeout)
#define FAAL_SNDMAX(itf)    (UplinkInterface[itf].sndmax)
#define FAAL_SNDNOR(itf)    (UplinkInterface[itf].sndnor)
#define FAAL_ATTR(itf)    (UplinkInterface[itf].attr)
//#define FAAL_TID(itf)    (g_faalitf[itf].tid)

void UplinkClearState(unsigned char itf);
int UplinkRecvPkt(unsigned char itf);
int UplinkSendPktG(unsigned char itf, uplink_pkt_tG *pkt); //���
int UplinkSendPktGAll(unsigned char itf, uplink_pkt_tG *pkt); //�㲥


#define UPRTN_OK    		0      	//���ͳɹ�
#define UPRTN_FAIL    	1    		//����ʧ��
#define UPRTN_OKRCV    	2    		//���ͳɹ�, �յ������
#define UPRTN_FAILRCV  	3    		//����֮ǰ�յ������
#define UPRTN_TIMEOUT 	4   		//���ͳ�ʱ

//flag = 0, not wait echo, 1-wait echo
int UplinkActiveSend(unsigned char itf, unsigned char flag, uplink_pkt_tG *psnd);

int UplinkLogon(unsigned char itf);
int UplinkLinkTest(unsigned char itf);
int UplinkCheckVer(unsigned char itf);
int UplinkDeviceCheck(unsigned char itf);
int UplinkLogonOut(unsigned char itf);

int IsEchoPkt(uplink_pkt_tG *pkt,unsigned char sndcmd);


char  CalcCheckSumB(char* P, unsigned short Len);
#endif /*_UPLINK_DL_H*/

