/**
* commport.h -- ͨ�Ŷ˿ڲ���ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-8
* ����޸�ʱ��: 2009-5-8
*/

#ifndef _PARAM_COMMPORT_H
#define _PARAM_COMMPORT_H

#define COMMFRAME_BAUD_300		0
#define COMMFRAME_BAUD_600		0x20
#define COMMFRAME_BAUD_1200		0x40
#define COMMFRAME_BAUD_2400		0x60
#define COMMFRAME_BAUD_4800		0x80
#define COMMFRAME_BAUD_7200		0xa0
#define COMMFRAME_BAUD_9600		0xc0
#define COMMFRAME_BAUD_19200		0xe0

#define COMMFRAME_STOPBIT_1		0
#define COMMFRAME_STOPBIT_2		0x10

#define COMMFRAME_NOCHECK		0
#define COMMFRAME_HAVECHECK		0x08

#define COMMFRAME_ODDCHECK		0
#define COMMFRAME_EVENCHECK		0x04

#define COMMFRAME_DATA_5		0
#define COMMFRAME_DATA_6		1
#define COMMFRAME_DATA_7		2
#define COMMFRAME_DATA_8		3


#define COMMPORT_RS485_1	0  //485���ƶ˿�
#define COMMPORT_RS485_2	1  //485���ƶ˿�
#define COMMPORT_RS485_3	2  //485���ƶ˿�
#define MAX_COMMPORT		3

//ʵ��Ӳ��485�˿�
#define CENMET_REALPORT		0//����
#define CASCADE_REALPORT		1//����
#define RS485BUS_REALPORT		2
#define MAX_485PORT             	3

typedef struct {
	unsigned char port;
	int baud;
	unsigned char parity;
	unsigned char databits;
	unsigned char stopbits;
	unsigned char type;
} cfg_para_485port_t;
	
#endif /*_PARAM_COMMPORT_H*/

