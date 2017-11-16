/**
* serial.c -- ��������ͨ��
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-6-8
* ����޸�ʱ��: 2009-6-8
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "include/basetype.h"
#include "include/debug.h"
#include "include/sys/task.h"
#include "include/sys/schedule.h"
#include "include/sys/uart.h"
#include "include/uplink/svrnote.h"
#include "uplink_pkt.h"
#include "uplink_dl.h"
#include "svrcomm.h"
#include "include/param/unique.h"
#define  QRCODE_UART	 UART_QRCODE //	4

static int SerialStarted = 0;

/**
* @brief ����ͨ������(��������)
*/
void SerialActiveTask(void)
{
	unsigned long ev;

	if(!SerialStarted) {
		ErrorLog("Serial not start, return\n");
		return;
	}

	UplinkClearState(UPLINKITF_SERIAL);

	while(1) {
		SvrCommPeekEvent(SVREV_NOTE, &ev);

		if(ev&SVREV_NOTE) {
			SvrNoteProc(UPLINKITF_SERIAL);
		}

		if(!UplinkRecvPkt(UPLINKITF_SERIAL)) {
			SvrMessageProc(UPLINKITF_SERIAL);
		}

		Sleep(10);
	}

	return;
}

/**
* @brief ����ͨ������(����������)
*/
static void *SerialPassiveTask(void *arg)
{
	char qrcodebuf[512]={0};
	int  recvlen = 0;
	memset(qrcodebuf, 0, 512);
	if(!SerialStarted) {
		ErrorLog("Serial not start, return\n");
		return 0;
	}
	UplinkClearState(UPLINKITF_SERIAL);

	Sleep(100);

	while(1) {

		recvlen = UartRecv(QRCODE_UART, qrcodebuf, 512);
		if(recvlen > 50)  //�յ���ά������
		{
			
			if( !strncmp(qrcodebuf, "GM", 2) ) //����
			{
				qrcodeValidity(qrcodebuf);
			}
		}
		memset(qrcodebuf, 0, 512);
		
		Sleep(10);
	}
	return 0;
}

/**
* @brief ��������ͨ������
* @param mode 0����������, 1��������
* @param baud ���ڲ�����
* @return �ɹ�����0, ʧ�ܷ���1
*/
DECLARE_INIT_FUNC(UplinkSerialStart);
int UplinkSerialStart(void)
{
	if(UartOpen(QRCODE_UART)) {
		PrintLog(0,"can not open uart %d\n", QRCODE_UART);
		return 1;
	}
	UartSet(QRCODE_UART, 115200, 8, 1, 'n');
	SerialStarted = 1;
	if(1) {
		SysCreateTask(SerialPassiveTask, NULL);
	}

	SET_INIT_FLAG(UplinkSerialStart);
	return 0;
}

/**
* @brief �Ӵ���ͨ�Žӿڶ�ȡһ���ֽ�
* @param buf �����ַ�ָ��
* @return �ɹ�0, ����ʧ��
*/
int SerialGetChar(unsigned char *buf)
{
	if(UartRecv(QRCODE_UART, buf, 1) > 0) return 0;
	else return 1;
}

/**
* @brief �򴮿�ͨ�Žӿڷ�������
* @param buf ���ͻ�����ָ��
* @param len ����������
* @return �ɹ�0, ����ʧ��
*/
int SerialRawSend(const unsigned char *buf, int len)
{
	return(UartSend(QRCODE_UART, buf, len));
}


