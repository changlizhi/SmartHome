/**
* crc.h -- ����CRC����ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-4-1
* ����޸�ʱ��: 2009-4-1
*/

#ifndef _LIB_CRC_H
#define _LIB_CRC_H

unsigned short CalculateCRC(const unsigned char *buffer, int count);
void CalculateCRCStep(const unsigned char *buffer, int count, unsigned short *pcrc);

#endif /*_LIB_CRC_H*/

