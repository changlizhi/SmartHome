/**
* rs485.c -- RS485�����ӿ�ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-4-24
* ����޸�ʱ��: 2009-4-27
*/

#ifndef _RS485_H
#define _RS485_H

//RS485 �˿���
#define RS485_PORTNUM	2

/**
* @brief ��λRS485�˿�
* @param port RS485�˿ں�
* @return 0�ɹ�, ����ʧ��
*/
int Rs485Reset(unsigned int port);
/**
* @brief ����RS485�˿ڲ����ʺ�����
* @param port �˿ں�
* @param baud ������
* @param databits ����λ, 5~8
* @param stopbits ֹͣλ, 1~2
* @param parity У��λ
*/
void Rs485Set(unsigned int port, int baud, int databits, int stopbits, char parity);

void rs485_setbaud(unsigned int port, unsigned int baud, unsigned char frame);
/**
* @brief ��RS485�˿ڷ�������
* @param port �˿ں�
* @param buf ���ͻ�����
* @param len ����������
* @param 0�ɹ�, ����ʧ��
*/
int Rs485Send(unsigned int port, const unsigned char *buf, int len);
/**
* @brief ��RS485�˿ڽ�������
* @param port �˿ں�
* @param buf ���ջ�����
* @param len ����������
* @return ʧ�ܷ���-1, �ɹ����ؽ��յ����ֽ���, ����0��ʾδ���յ�����
*/
int Rs485Recv(unsigned int port, unsigned char *buf, int len);

/**
* @brief ��סRs485�˿�
* @param port �˿ں�
*/
void Rs485Lock(unsigned int port);
/**
* @brief ����Rs485�˿�
* @param port �˿ں�
*/
void Rs485Unlock(unsigned int port);

#define RS485_BITMASK   	0x03
#define RS485_BIT5   		0x00
#define RS485_BIT6   		0x01
#define RS485_BIT7   		0x02
#define RS485_BIT8   		0x03

#define RS485_STOPMASK    0x04
#define RS485_STOP1    	0x00
#define RS485_STOP2    	0x04

#define RS485_PARITYMASK    0x38
#define RS485_NOPARITY   	0x00
#define RS485_ODDPARITY    	0x08
#define RS485_EVENPARITY    0x18
#define RS485_1PARITY    	0x30
#define RS485_0PARITY    	0x38

#define MAXNUM_RS485    4
#endif /*_RS485_H*/
