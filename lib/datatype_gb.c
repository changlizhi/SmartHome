/**
* datatype_gb.c -- ������������ת������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-8
* ����޸�ʱ��: 2009-5-8
*/

#include "include/lib/bcd.h"
#include "include/lib/datatype_gb.h"

/**
* @brief ������������02ת��Ϊ����ֵ
* @param psrc ���뻺����ָ��
* @return ת����Ĺ���ֵ(��0.01kWΪ��λ)
*/
int Sfloat02ToPower(const unsigned char *psrc)
{
	int rtn, i, base;
	unsigned char uc;

	rtn = (int)(psrc[1]&0x0f);
	rtn *= 100;
	uc = (psrc[0]&0xf0)>>4;
	uc *= 10;
	uc += psrc[0]&0x0f;
	rtn += (int)uc&0xff;

	uc = (psrc[1]&0xe0)>>5;
	uc = (~uc)&0x07;

	base = (int)uc;
	base--;
	if(base < 0) {
		rtn /= 10;
	}
	else {
		for(i=0; i<base; i++) rtn *= 10;
	}

	if(psrc[1]&0x10) rtn *= -1;

	return(rtn);
}

/**
* @brief ����ֵת��Ϊ������������02
* @param ����ֵ(��0.01kWΪ��λ)
* @param pdst ���������ָ��
*/
void PowerToSfloat02(int src, unsigned char *pdst)
{
	int i;
	unsigned char flag, uc;

	if(src < 0) {
		src *= -1;
		flag = 1;
	}
	else flag = 0;

	//Ϊ�˿�½���Ʋ���һ���Լ��...	
	if((src < 99900) && (0 == (src%100))) {
		src /= 100;

		uc = 0x80;
		if(flag) uc |= 0x10;
		uc += (unsigned char)(src/100);
		pdst[1] = uc;

		src %= 100;
		uc = (unsigned char)(src/10)<<4;
		uc += (unsigned char)(src%10);
		pdst[0] = uc;

		return;
	}

	for(i=1; i<7; i++) {
		if(src < 1000) break;
		src /= 10;
	}
	if(src >= 1000) src = 999;

	uc = i;
	uc = (~uc)&0x07;
	uc = (uc<<5)&0xe0;
	if(flag) uc |= 0x10;

	uc += (unsigned char)(src/100);
	pdst[1] = uc;

	src %= 100;

	uc = (unsigned char)(src/10)<<4;
	uc += (unsigned char)(src%10);
	pdst[0] = uc;
}

/**
* @brief ������������03ת��Ϊ������ֵ
* @param psrc ���뻺����ָ��
* @return ת����ĵ�����ֵ(��kWhΪ��λ)
*/
int Sbcd03ToEnergy(const unsigned char *psrc)
{
	int tmp;

	tmp = (int)psrc[3] & 0x0f;
	tmp *= 1000000;
	tmp += BcdToUnsigned(psrc, 3);

	if(psrc[3]&0x40) {
		if(tmp > MAX_GENE_MWH) tmp = MAX_GENE_MWH;
		tmp *= 1000;
	}
	if(psrc[3]&0x10) tmp *= -1;

	return(tmp);
}

/**
* @brief ������ֵת��Ϊ������������03
* @param ������ֵ(��kWhΪ��λ)
* @param pdst ���������ָ��
*/
void EnergyToSbcd03(int src, unsigned char *pdst)
{
	unsigned char flag;

	if(src < 0) {
		flag = 0x10;
		src *= -1;
	}
	else flag = 0;

	if(src > 9999999) {
		src /= 1000;
		flag |= 0x40;
		if(src > 9999999) src = 9999999;
	}

	UnsignedToBcd(src, pdst, 4);
	pdst[3] &= 0x0f;
	pdst[3] |= flag;
}

