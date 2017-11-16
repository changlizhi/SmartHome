/**
* localsvr.c -- ������̫��ͨ��(������ģʽ)
* 
* ����: chenshugao
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
static int SockLocalSvr = -1;
static int localSock	     = -1; //�ͻ���socket
static int cSockConnectNum = 0;
//static struct sockaddr AddrTcpSvr;

/**
* @brief ��̫��ͨ�������ʼ��
* @return �ɹ�0, ����ʧ��
*/
static int LocalSvrNetInit(void)
{
  	int nResult=0;
	struct sockaddr_in addr;
//	int ctlflag;
	if(SockLocalSvr >=0)
		return 0;
	SockLocalSvr = socket(AF_INET, SOCK_STREAM, 0);

	if(SockLocalSvr < 0) {
		PrintLog(0,"create local socket error.\r\n");
		return 1;
	}

	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	addr.sin_port = htons(9998);
	addr.sin_addr.s_addr = htonl(INADDR_ANY);

	if(bind(SockLocalSvr, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
		PrintLog(0,"bind error(%d).\r\n", errno);
		close(SockLocalSvr);
		SockLocalSvr = -1;
		return 1;
	}

	PrintLog(0,"ether local server listen at port %d...\n",9998);
	
	nResult = listen(SockLocalSvr, 5);//SOMAXCONN);
        if ( -1 == nResult)
        {
        	close(SockLocalSvr);
        }
	
	return 0;
}

static int WaitClientConnect()
{
  struct sockaddr_in rec_addr;
  socklen_t rec_len = sizeof(rec_addr);
  if(localSock>=0)
  	return localSock;
  localSock = accept(SockLocalSvr,  (struct sockaddr *)&rec_addr,&rec_len);
  if(cSockConnectNum)
  {
  	close(localSock);
	cSockConnectNum = 0;
  }
  else 
  {
  	cSockConnectNum = 1;
  }
  return localSock;	
}
/**
* @brief ��̫��ͨ������
*/
static void *LocalSvrTask(void *arg)
{
	unsigned long ev;
	UplinkClearState(UPLINKITF_LOCALSVR);
	LocalSvrNetInit();//����Tcp ����

	while(1) {
           /*  	if(ParaTermG.reg.autoflag == 0) //����δע��
		{
			Sleep(100);
			continue;
		}*/
		if(WaitClientConnect() >= 0)
		 {
		 	SvrCommPeekEvent(SVREV_NOTE, &ev);

			if(ev&SVREV_NOTE) {
				SvrNoteProc(UPLINKITF_LOCALSVR);
			}
			
			while(!UplinkRecvPkt(UPLINKITF_LOCALSVR)) {
					
				SvrMessageProc(UPLINKITF_LOCALSVR);
			}
		}
		if(exitflag)
		{
			close(localSock);
			break;
		}
		Sleep(10);
	}
}

/**
* @brief ��̫��ͨ�ų�ʼ��
* @return �ɹ�0, ����ʧ��
*/
DECLARE_INIT_FUNC(LocalSvrInit);
int LocalSvrInit(void)
{
	SysCreateTask(LocalSvrTask, NULL);

	SET_INIT_FLAG(LocalSvrInit);
	return 0;
}

static unsigned char LocalSvrRcvBuffer[2048];
static int LocalSvrRcvLen = 0;
static int LocalSvrRcvHead = 0;

/**
* @brief ����̫��ͨ�Žӿڶ�ȡһ���ֽ�
* @param buf �����ַ�ָ��
* @return �ɹ�0, ����ʧ��
*/
int LocalSvrGetChar(unsigned char *buf)
{
	if(SockLocalSvr < 0 ||localSock < 0 ) return 1;

	if(LocalSvrRcvLen <= 0) 
	{
		//ether_recvlen = recv(sock_ether, ether_recvbuf, 2048, 0);
		LocalSvrRcvLen = recv(localSock, LocalSvrRcvBuffer, 2048, MSG_DONTWAIT);
		if(((LocalSvrRcvLen < 0) && (errno != EWOULDBLOCK)) ||
				(LocalSvrRcvLen == 0)) {
			PrintLog(0, "connection corrupted(%d,%d).\n", LocalSvrRcvLen, errno);
			CLOSE_SOCKET(localSock);
			cSockConnectNum = 0;
			return 1;
		}
		else if(LocalSvrRcvLen < 0) {
			
			return 1;
		}
		else {
			LocalSvrRcvLen = 0;
		}
	}

	*buf = LocalSvrRcvBuffer[LocalSvrRcvHead++];
	LocalSvrRcvLen--;
	return 0;
}

/**
* @brief ����̫��ͨ�Žӿڷ�������
* @param buf ���ͻ�����ָ��
* @param len ����������
* @return �ɹ�0, ����ʧ��
*/
int LocalSvrRawSend(const unsigned char *buf, int len)
{
	if(SockLocalSvr < 0 ||localSock < 0 ) return 1;

	if(send(localSock, buf, len, MSG_NOSIGNAL) < 0) {
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
	CLOSE_SOCKET(localSock);
	cSockConnectNum = 0;
	return 1;
}

