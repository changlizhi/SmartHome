/**
* version.h -- �汾��ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-3-31
* ����޸�ʱ��: 2009-5-6
*/

#ifndef _VERSION_H
#define _VERSION_H

//���̰汾��

//����Լ�汾��Ϣ 
//�汾��ΪBCD�룬��01-99��
#define VERSION_MAJOR		01     //���汾��
#define VERSION_SUBMAJOR	01     //�ΰ汾��
#define VERSION_MINOR		04    //С�汾 

//�汾��������
#if 0
#define RELEASE_DATE_YEAR	0x09
#define RELEASE_DATE_MONTH	0x05
#define RELEASE_DATE_DAY	0x05
#else
extern const unsigned char _mk_year;
extern const unsigned char _mk_month;
extern const unsigned char _mk_day;
extern const unsigned char _mk_hour;
extern const unsigned char _mk_minute;
#endif
//Ӧ����Ҫ������������汾��
//ע��ÿ����ʽ����ǰ�����added by yzl. 2011.6.15
#define VERSION_PACK_MAJOR		03 
#define VERSION_PACK_MINOR		01
#define VERSION_PACK_HARD		4
/*
@��Լ���ͣ��ɺ����ĳЩʡ����������
@��Ҫѡ��ĳʡ�������Ӧ�ĺ����,�����±��롣
*/

#define	TYPE_NWTY			0	//����ͨ��()
#define	TYPE_S3C2440  		1 	//linux Arm9�汾
#define	TYPE_S3C6410  		2 	//linux Arm9�汾
#define	TYPE_ANDROID  		3 	//Android �汾

#define 	GWVERSION	               TYPE_NWTY/*����ÿ���汾*/			


extern const char *VerStringProj[];
#define STRING_PROJECT		VerStringProj[GWVERSION]
extern const char *hard_cpu;//CPU����
extern const char *hard_type;//Ӳ������

#endif /*_VERSION_H*/

