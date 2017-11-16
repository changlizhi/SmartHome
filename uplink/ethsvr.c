/**
* ethsvr.c -- ��̫��ͨ��(������ģʽ)
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-19
* ����޸�ʱ��: 2009-5-19
*/

#include <stdio.h>
#include <string.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <fcntl.h>
#include <arpa/inet.h>
#include <sys/errno.h>

#include "include/basetype.h"
#include "include/debug.h"
#include "include/sys/schedule.h"
#include "include/sys/task.h"
#include "include/param/term.h"
#include "include/param/unique.h"
#include "uplink_pkt.h"
#include "uplink_dl.h"
#include "svrcomm.h"
#include "include/uplink/svrnote.h"
static int SockEthSvr = -1;
static struct sockaddr AddrEthSvr;
#define CLOSE_SOCKET(sock)   { \
	if((sock) >= 0) { \
		close(sock); \
		sock = -1; \
	}}
/**
* @brief ��̫��ͨ�������ʼ��
* @return �ɹ�0, ����ʧ��
*/
static int EthSvrNetInit(void)//crt����UDP���� 
{
	struct sockaddr_in addr;
	int ctlflag;

	SockEthSvr = socket(AF_INET, SOCK_DGRAM, 0);
	//SOCK_DGRAM
   //	SockEthSvr = socket(AF_INET, SOCK_STREAM, 0);
	if(SockEthSvr < 0) {
		PrintLog(0,"create socket error.\r\n");
		return 1;
	}

	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	addr.sin_port = htons(ParaUniG.termip.portlisten);
	//addr.sin_port = htons(8888);
	//addr.sin_port = htons(9999);
	addr.sin_addr.s_addr = htonl(INADDR_ANY);

	if(bind(SockEthSvr, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
		close(SockEthSvr);
		SockEthSvr = -1;
		return 1;
	}


	ctlflag = fcntl(SockEthSvr, F_GETFL);
	ctlflag |= O_NONBLOCK;
	fcntl(SockEthSvr, F_SETFL, ctlflag);

	return 0;
}

static int EtherDisconnect(void)
{
	CLOSE_SOCKET(SockEthSvr);
	return 0;
}
/**
* @brief ��̫��ͨ������
*/
static void *EthSvrTask(void *arg)
{
	unsigned long ev;
	UplinkClearState(UPLINKITF_ETHMTN);
	EthSvrNetInit();//����UDP����
	while(1) {
		/*if(ParaTermG.reg.autoflag == 0) //����δע��
		{
			Sleep(100);
			continue;
		}*/
		while(!UplinkRecvPkt(UPLINKITF_ETHMTN)) {
			
			SvrMessageProc(UPLINKITF_ETHMTN);
		}

		Sleep(10);
		if(exitflag)
		{
			EtherDisconnect();
			break;
		}
	}
}

/**
* @brief ��̫��ͨ�ų�ʼ��
* @return �ɹ�0, ����ʧ��
*/
DECLARE_INIT_FUNC(EthSvrInit);
int EthSvrInit(void)
{
	SysCreateTask(EthSvrTask, NULL);

	SET_INIT_FLAG(EthSvrInit);
	return 0;
}

static unsigned char EthSvrRcvBuffer[2048];
static int EthSvrRcvLen = 0;
static int EthSvrRcvHead = 0;

/**
* @brief ����̫��ͨ�Žӿڶ�ȡһ���ֽ�
* @param buf �����ַ�ָ��
* @return �ɹ�0, ����ʧ��
*/
int EthSvrGetChar(unsigned char *buf)
{
	unsigned int addrlen;

	if(SockEthSvr < 0) return 1;

	if(EthSvrRcvLen <= 0) {
		addrlen = sizeof(AddrEthSvr);
		EthSvrRcvLen = recvfrom(SockEthSvr, EthSvrRcvBuffer, 2048, 0, &AddrEthSvr, &addrlen);
		if(EthSvrRcvLen <= 0) return 1;
		else EthSvrRcvHead = 0;
	}

	*buf = EthSvrRcvBuffer[EthSvrRcvHead++];
	EthSvrRcvLen--;
	return 0;
}

/**
* @brief ����̫��ͨ�Žӿڷ�������
* @param buf ���ͻ�����ָ��
* @param len ����������
* @return �ɹ�0, ����ʧ��
*/
int EthSvrRawSend(const unsigned char *buf, int len)
{
	if(SockEthSvr < 0) return 1;
	struct sockaddr_in sin;
	memcpy(&sin,&AddrEthSvr, sizeof(sin));
	char IP[32] = {0};
	sprintf(IP, inet_ntoa(sin.sin_addr));
	DebugPrint(0,"IP:%s,Port:%d  \n",IP,sin.sin_port);
	sin.sin_port = 9999;
	//sendto(SockEthSvr, buf, len, 0, &AddrEthSvr, sizeof(AddrEthSvr));
	sin.sin_port = 9999;
	sendto(SockEthSvr, buf, len, 0, &AddrEthSvr, sizeof(AddrEthSvr));
	return 0;
}

