/**
* capconf.h -- ��������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-10
* ����޸�ʱ��: 2009-5-10
*/

#ifndef _PARAM_CAPCONF_H
#define _PARAM_CAPCONF_H

#define MAX_CET              		10   //�๦�ܱ�������
#define MAX_METER    		255 //�����/����������
#define MAX_METP			MAX_METER   //����������#define MAX_METP1			64 //���ڲ�����
#define MAX_CENMETP		1     //���๦�ܲ�������, �ز���ƵĲ������ֻ�ܴ������

#define MAX_PLCMET			(MAX_METP-MAX_CENMETP)  //����ز�����
#define PLC_BASEMETP		(MAX_CENMETP+1)  //�ز�����ʼ�������(���) ��2�ű�ʼΪ��ͨ�ز���

#define IMPORTANT_BASEMETP            1201
#ifdef DEBUGMODE
#define MAX_IMPORTANT_USER		16//6   //����ص��û�����
#else
#define MAX_IMPORTANT_USER		6   //����ص��û�����	
#endif
#define IMPORTANT_ENDMETP              (IMPORTANT_BASEMETP+MAX_IMPORTANT_USER)

#define METYPE_ELEMET 0x01/*������ӱ�*/
#define METYPE_MENMET 2/*��е��*/
#define METYPE_SIMFUNCMET 3/*���׶๦�ܱ�*/
#define METYPE_MULFUNCMET 8/*�๦���ܱ�*/
#endif /*_PARAM_CAPCONF_H*/

