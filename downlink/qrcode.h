/**
* qrcode.h -- ���ն�ά���ͷ����
* 
* ����: chenshugao
* ����ʱ��: 2014-5-28
* ����޸�ʱ��: 2014-5-28
*/

#ifndef _QRCODE_H
#define _QRCODE_H

extern void *QrCodeTask(void *arg);
typedef struct {
	unsigned short addr;   			//�豸��ַ
	unsigned char runstate[4];  //״̬��
} ctrlcabinet_t;  //��ǰ��
extern ctrlcabinet_t  ctrlstate[4];

extern int ctrlnum;


#endif /*_QRCODE_H*/

