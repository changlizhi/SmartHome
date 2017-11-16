/**
* svrnote.h -- ������ͨ��������������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-19
* ����޸�ʱ��: 2009-5-19
*/

#ifndef _SVRCOMM_NOTE_H
#define _SVRCOMM_NOTE_H

#define SVREV_NOTE				0x00000001

#define SVRNOTEMASK_ALARM		0x80000000

#define SVRNOTEID_ALARM			0x00000002
#define SVRNOTEID_UPSENSOR     	0x00000004
#define SVRNOTEID_UPMONTH      	0x00000008
#define SVRNOTEID_UPIMP           	0x00000010
#define SVRNOTEID_UPMETSTATE   0x00000020
#define SVRNOTEID_UPMETINFO   	0x00000040

void SvrCommNote(int id);

extern int    UpdateSensorId;

#endif /*_SVRCOMM_NOTE_H*/

