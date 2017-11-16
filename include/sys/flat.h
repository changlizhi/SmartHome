/**
* flat.h -- ƽ������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-15
* ����޸�ʱ��: 2009-5-15
*/

#ifndef _SYS_FLAT_H
#define _SYS_FLAT_H

//copy from driver.ע�⣬��driver�нṹ�Ķ�����˴������
#define FLATID_START		0
#define FLATID_IMETENE	FLATID_START	
#define FLATID_PULSE		1
#define FLATID_RUNSTATE	2
#define FLATID_END		3
#define MAX_SECTOR		FLATID_END

#define BUFFER_SIZE		1024

typedef struct {
	unsigned int id;
	unsigned short add_start;
	unsigned short add_max;
} sector_conf_t;


/**
* @brief ��ȡFLAT�ļ�����
* @param sector �ļ�������(0~2)
* @param buf ������ָ��
* @param len ����������
* @return �ɹ�����ʵ�ʶ�ȡ����, ʧ�ܷ���-1
*/
int ReadFlatFile(unsigned int sector, unsigned char *buf, int len);

/**
* @brief д��FLAT�ļ�����
* @param sector �ļ�������(0~2)
* @param buf ������ָ��
* @param len ����������
* @return �ɹ�����ʵ��д�볤��, ʧ�ܷ���-1
*/
int WriteFlatFile(unsigned int sector, const unsigned char *buf, int len);

#endif /*_SYS_FLAT_H*/


