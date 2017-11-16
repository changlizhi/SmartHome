/**
* uplink_dl.h -- ����ͨ��������·��
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-18
* ����޸�ʱ��: 2009-5-18
*/

#ifndef _DOWNLINK_DL_H
#define _DOWNLINK_DL_H


//����ͨ���ŵ����

#define DOWNLINKITF_IMET645			0   //����

#define DOWNLINKITF_NUM			1

#define DOWNLINKATTR_NOECHO    0x01    //�������Ͳ�����Ӧ(������ŵ�)


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
} downlinkitf_t;

extern const downlinkitf_t DownlinkInterface[DOWNLINKITF_NUM];
#define DOWNLINK_RCVBUF(itf)		(DownlinkInterface[itf].rcvbuf)
#define DOWLINK_SNDBUF(itf)			(DownlinkInterface[itf].sndbuf)
#define DOWLINK_RCVMAX(itf)			(DownlinkInterface[itf].rcvmax)
#define DOWLINK_TIMEOUT(itf)		(DownlinkInterface[itf].timeout)
#define DOWLINK_SNDMAX(itf)			(DownlinkInterface[itf].sndmax)
#define DOWLINK_SNDNOR(itf)			(DownlinkInterface[itf].sndnor)
#define DOWLINK_ATTR(itf)			(DownlinkInterface[itf].attr)

#define DWON_FAAL_RCVBUF(itf)   		(DownlinkInterface[itf].rcvbuf)
#define DWON_FAAL_SNDBUF(itf)    	(DownlinkInterface[itf].sndbuf)
#define DWON_FAAL_RCVMAX(itf)   		(DownlinkInterface[itf].rcvmax)
#define DWON_FAAL_TIMEOUT(itf)    	(DownlinkInterface[itf].timeout)
#define DWON_FAAL_SNDMAX(itf)    	(DownlinkInterface[itf].sndmax)
#define DWON_FAAL_SNDNOR(itf)    	(DownlinkInterface[itf].sndnor)
#define DWON_FAAL_ATTR(itf)    		(DownlinkInterface[itf].attr)

void DownlinkClearState(unsigned char itf);
int DownlinkRecvPkt(unsigned char itf);


//char  CalcCheckSumB(char* P, unsigned short Len);
#endif /*_UPLINK_DL_H*/

