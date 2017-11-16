/**
* grpbin.h -- ������Ⱥ���ļ�����ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-6
* ����޸�ʱ��: 2009-5-6
*/

#ifndef _STORAGE_GRPBIN_H
#define _STORAGE_GRPBIN_H

typedef struct {
	char *pfile;
	int itemlen;  //��Ŀ����
	int itemnum;  //��Ŀ��Ŀ
	unsigned short crctemp;
	char flag;
} grpbin_ref_t;

/**
* @brief ��һ��ȺBIN�ļ�
* @param file �ļ���
* @param magic �ļ���ʶ��
* @param flag �򿪷�ʽ. 'r':��ȡ��ʽ; 'w':д��ʽ
* @param pref �ļ���������ָ��
* @return �ɹ�����0,����ʧ��
*/
int OpenGrpBinFile(const char *file, unsigned long magic, char flag, grpbin_ref_t *pref);
/**
* @brief ��ȺBIN�ļ��ж�ȡһ����Ŀ
* @param pref �ļ���������ָ��
* @param buffer ������ָ��
* @param len ����������
* @return �ɹ�����ʵ�ʶ�ȡ����,ʧ�ܷ���-1
*/
int ReadGrpBinFileItem(grpbin_ref_t *pref, unsigned char *buffer, int len);
/**
* @brief ��ȺBIN�ļ���д��һ����Ŀ
* @param pref �ļ���������ָ��
* @param buffer ������ָ��
* @param len ����������
* @return �ɹ�����0,����ʧ��
*/
int WriteGrpBinFileItem(grpbin_ref_t *pref, unsigned char *buffer);
/**
* @brief �ر�һ��ȺBIN�ļ�
* @param pref �ļ���������ָ��
*/
void CloseGrpBinFile(grpbin_ref_t *pref);

#endif /*#ifndef _STORAGE_GRPBIN_H*/

