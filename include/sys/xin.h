/**
* xin.c -- ��ini�ı������ļ�����ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-4-22
* ����޸�ʱ��: 2009-4-22
*/

#ifndef _XIN_H
#define _XIN_H

//�ļ�����ָ��
#define XINREF		char *

/**
* @brief �������ļ�
* @param filename ���ļ���
* @param flag �򿪷�ʽ. 'r':��ȡ��ʽ; 'w':д��ʽ
* @return �ɹ�ʱ�����ļ�����ָ�룬����ΪNULL(��ָ��)
*/
XINREF XinOpen(const char *filename, char flag);
/**
* @brief �ر������ļ�
* @param pf �ļ�����ָ��
*/
void XinClose(XINREF pf);

/**
* @brief ��ȡһ������
* @param pf �ļ�����ָ��
* @param varname ������
* @param defvalue ȱʡֵ
* @return �ɹ����ر���ֵ, ʧ�ܷ���ȱʡֵ
*/
int XinReadInt(XINREF pf, const char *varname, int defvalue);
/**
* @brief ��ȡһ���ַ���
* @param pf �ļ�����ָ��
* @param varname ������
* @param buffer ����ָ��
* @param len ���泤��
* @return �ɹ��ַ�������, ʧ�ܷ���-1
*/
int XinReadString(XINREF pf, const char *varname, char *buffer, int len);
/**
* @brief ��ȡһ��ʮ����������
* @param pf �ļ�����ָ��
* @param varname ������
* @param buffer ����ָ��
* @param len ���泤��
* @return �ɹ���������, ʧ�ܷ���-1
*/
int XinReadHex(XINREF pf, const char *varname, unsigned char *buffer, int len);

/**
* @brief д��һ������
* @param pf �ļ�����ָ��
* @param varname ������
* @param value ����ֵ
* @param hex д���ʽ, �������, ���ӡ��'0x...'��ʽ
* @return �ɹ�ʱ����0�����򷵻ط���ֵ
*/
int XinWriteInt(XINREF pf, const char *varname, int value, int hex);
/**
* @brief д��һ���ַ���
* @param pf �ļ�����ָ��
* @param varname ������
* @param str ����ֵ
* @return �ɹ�ʱ����0�����򷵻ط���ֵ
*/
int XinWriteString(XINREF pf, const char *varname, const char *str);
/**
* @brief д��һ��ʮ����������
* @param pf �ļ�����ָ��
* @param varname ������
* @param str ����ֵ
* @return �ɹ�ʱ����0�����򷵻ط���ֵ
*/
int XinWriteHex(XINREF pf, const char *varname, const unsigned char *buffer, int len);

#endif /*_XIN_H*/

