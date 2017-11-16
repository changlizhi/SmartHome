/**
* uart.h -- UART�����ӿ�ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-4-23
* ����޸�ʱ��: 2009-4-23
*/

#ifndef _UART_H
#define _UART_H

/*by ydl modify 2011-05-05*/
//#define UART_PORTNUM		5
#define UART_PORTNUM		2

#define UART_RS485_0		0
#define UART_QRCODE			1
/*end*/

/**
* @brief ��һ��UART�˿�
* @param port �˿ں�, 0~4
* @return 0�ɹ�, ����ʧ��
*/
int UartOpen(unsigned int port);
/**
* @brief �ر�һ���Ѵ򿪵�UART�˿�
* @param port �˿ں�, 0~4
*/
void UartClose(unsigned int port);

/**
* @brief ����UART�˿ڲ�����
* @param port �˿ں�, 0~4
* @param baud ������
*/
void UartSetBaudrate(unsigned int port, int baud);
/**
* @brief ����UART�˿�����
* @param port �˿ں�, 0~4
* @param databits ����λ, 5~8
* @param stopbits ֹͣλ, 1~2
* @param parity У��λ
*/
void UartSetParity(unsigned int port, int databits,int stopbits, char parity);
/**
* @brief ����UART�˿ڲ����ʺ�����
* @param port �˿ں�, 0~4
* @param baud ������
* @param databits ����λ, 5~8
* @param stopbits ֹͣλ, 1~2
* @param parity У��λ
*/
void UartSet(unsigned int port, int baud, int databits, int stopbits, char parity);

/**
* @brief ��UART�˿ڷ�������
* @param port �˿ں�, 0~4
* @param buf ���ͻ�����
* @param len ����������
* @param 0�ɹ�, ����ʧ��
*/
int UartSend(unsigned int port, const unsigned char *buf, int len);
/**
* @brief ��UART�˿ڽ�������
* @param port �˿ں�, 0~4
* @param buf ���ջ�����
* @param len ����������
* @return ʧ�ܷ���-1, �ɹ����ؽ��յ����ֽ���, ����0��ʾδ���յ�����
*/
int UartRecv(unsigned int port, unsigned char *buf, int len);

/**
* @brief ��ȡUART�˿ڵ��ļ���(pppʹ��)
* @param port �˿ں�, 0~4
* @return ʧ�ܷ���-1, �ɹ������ļ���
*/
int UartGetFid(unsigned int port);

#endif /*_UART_H*/
