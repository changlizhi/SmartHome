/**
* datatype_gb.c -- ������������ת������ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-8
* ����޸�ʱ��: 2009-5-8
*/

#ifndef _DATATYPE_GB_H
#define _DATATYPE_GB_H

int Sfloat02ToPower(const unsigned char *psrc);
void PowerToSfloat02(int src, unsigned char *pdst);

#define MAX_GENE_MWH	2000000

int Sbcd03ToEnergy(const unsigned char *psrc);
void EnergyToSbcd03(int src, unsigned char *pdst);

#endif /*_DATATYPE_GB_H*/

