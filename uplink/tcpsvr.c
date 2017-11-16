/**
* ethsvr.c -- ��̫��ͨ��(������ģʽ)
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-19
* ����޸�ʱ��: 2009-5-19
*/

#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <fcntl.h>
#include <arpa/inet.h>
#include <sys/errno.h>
#include <sys/ioctl.h>


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
#define CLOSE_SOCKET(sock)   { \
	if((sock) >= 0) { \
		close(sock); \
		sock = -1; \
	}}
static int SockTcpSvr = -1;
static int cSock	     = -1; //�ͻ���socket
static int cSockConnectNum = 0;
//static struct sockaddr AddrTcpSvr;

static int EtherDisconnect(void)
{
	CLOSE_SOCKET(SockTcpSvr);
	return 0;
}
/**
* @brief ��̫��ͨ�������ʼ��
* @return �ɹ�0, ����ʧ��
*/
static int TcpSvrNetInit(void)
{
  	int nResult=0;
	struct sockaddr_in addr;
//	int ctlflag;

	SockTcpSvr = socket(AF_INET, SOCK_STREAM, 0);

	if(SockTcpSvr < 0) {
		PrintLog(0,"create socket error.\r\n");
		return 1;
	}

	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	addr.sin_port = htons(9997);
	addr.sin_addr.s_addr = htonl(INADDR_ANY);

	if(bind(SockTcpSvr, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
		PrintLog(0,"bind error(%d).\r\n", errno);
		close(SockTcpSvr);
		SockTcpSvr = -1;
		return 1;
	}

	PrintLog(0,"ether server listen at port %d...\n",9997);
	
	nResult = listen(SockTcpSvr, 5);//SOMAXCONN);
        if ( -1 == nResult)
        {
        	close(SockTcpSvr);
        }
	
	return 0;
}

static int WaitClientConnect()
{
  struct sockaddr_in rec_addr;
  socklen_t rec_len = sizeof(rec_addr);
  if(cSock>=0)
  	return cSock;
  cSock = accept(SockTcpSvr,  (struct sockaddr *)&rec_addr,&rec_len);
  if(cSockConnectNum)
  {
  	close(cSock);
	cSockConnectNum = 0;
  }
  else 
  {
  	cSockConnectNum = 1;
  }
  return cSock;	
}
/**
* @brief ��̫��ͨ������
*/
static void *TcpSvrTask(void *arg)
{
	unsigned long ev;
	UplinkClearState(UPLINKITF_TCPSVR);
	TcpSvrNetInit();//����Tcp ����

	while(1) {
		
		/*if(ParaTermG.reg.autoflag == 0) //����δע��
		{
			Sleep(100);
			continue;
		}*/
		if(WaitClientConnect() >= 0)
		 {
		    	SvrCommPeekEvent(SVREV_NOTE, &ev);

			if(ev&SVREV_NOTE) {
				SvrNoteProc(UPLINKITF_TCPSVR);
			}
			
			while(!UplinkRecvPkt(UPLINKITF_TCPSVR)) {
					
				SvrMessageProc(UPLINKITF_TCPSVR);					
			}
		}
		if(exitflag)
		{
			EtherDisconnect();
			break;
		}
		Sleep(10);
	}
}

/**
* @brief ��̫��ͨ�ų�ʼ��
* @return �ɹ�0, ����ʧ��
*/
DECLARE_INIT_FUNC(TcpSvrInit);
int TcpSvrInit(void)
{
	SysCreateTask(TcpSvrTask, NULL);

	SET_INIT_FLAG(TcpSvrInit);
	return 0;
}

static unsigned char TcpSvrRcvBuffer[2048];
static int TcpSvrRcvLen = 0;
static int TcpSvrRcvHead = 0;

/**
* @brief ����̫��ͨ�Žӿڶ�ȡһ���ֽ�
* @param buf �����ַ�ָ��
* @return �ɹ�0, ����ʧ��
*/
int TcpSvrGetChar(unsigned char *buf)
{
	if(SockTcpSvr < 0 ||cSock < 0 ) return 1;

	if(TcpSvrRcvLen <= 0) 
	{
		//ether_recvlen = recv(sock_ether, ether_recvbuf, 2048, 0);
		TcpSvrRcvLen = recv(cSock, TcpSvrRcvBuffer, 2048, MSG_DONTWAIT);
		if(((TcpSvrRcvLen < 0) && (errno != EWOULDBLOCK)) ||
				(TcpSvrRcvLen == 0)) {
			PrintLog(LOGTYPE_SHORT, "connection corrupted(%d,%d).\n", TcpSvrRcvLen, errno);
			CLOSE_SOCKET(cSock);
			cSockConnectNum = 0;
			return 1;
		}
		else if(TcpSvrRcvLen < 0) {
			return 1;
		}
		else {
			TcpSvrRcvHead = 0;
		}
	}

	*buf = TcpSvrRcvBuffer[TcpSvrRcvHead++];
	TcpSvrRcvLen--;
	return 0;
}

/**
* @brief ����̫��ͨ�Žӿڷ�������
* @param buf ���ͻ�����ָ��
* @param len ����������
* @return �ɹ�0, ����ʧ��
*/
int TcpSvrRawSend(const unsigned char *buf, int len)
{
	if(SockTcpSvr < 0 ||cSock < 0 ) return 1;

	if(send(cSock, buf, len, MSG_NOSIGNAL) < 0) {
		DebugPrint(1, "send to client fail\r\n");
		goto mark_failend;
	}
	PrintHexLog(0, buf, len);
	return 0;

#if 0
	//wait until send buffer empty
	for(i=0; i<100; i++) {
		osh_sleep(10);

		if(ioctl(sock_ether, SIOCOUTQ, &buflen)) goto mark_failend;

		//debug_print(1, "buflen = %d\r\n", buflen);
		if(0 == buflen) return 0;
	}
#endif

mark_failend:
	PrintLog(LOGTYPE_SHORT, "connection corrupted.\r\n");
	PrintLog(0,"\n connect courrupted. \n");
	CLOSE_SOCKET(cSock);
	return 1;
}

