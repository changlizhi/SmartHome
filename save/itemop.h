#ifndef _ITEMOP_H
#define _ITEMOP_H


#define ITEMOP_LOWLEVEL    0
#define ITEMOP_HIGHLEVEL    0x11
typedef struct {
	unsigned short id;  //�������ʶ
	unsigned short maxlen;   //��������󳤶�
	unsigned char *buf;   //����ָ��
	unsigned short actlen;   //������ʵ�����ݳ���
	//unsigned char mid;   //�������
	unsigned short mid;
	unsigned char level;   //��������
	unsigned char itf;   //�������ڽӿ�
} itemop_t;


#define ITORTN_OK    0   //���������д�ɹ�
#define ITORTN_INVALID    1   //�Ƿ����������
#define ITORTN_PWDERR    2   //�������
#define ITORTN_OPFAIL    3   //������дʧ��
#define ITORTN_OPTIMEOUT 4

int write_item(itemop_t *op);
int read_item(itemop_t *op);

//void set_savflag(unsigned char flag);
//void clear_savflag(void);
//void deal_savflag(void);
#endif

