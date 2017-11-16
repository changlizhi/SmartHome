/**
* plmdb.h -- �ز�������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-22
* ����޸�ʱ��: 2009-5-22
*/

#ifndef _PLMDB_H
#define _PLMDB_H

#include "include/param/capconf.h"
#include "include/lib/dbtime.h"
#include "include/environment.h"

#define PLDATA_EMPTY		0x00 //�����ЧֵΪ0xff
#define PLTIME_EMTPY		0xffff

#define PLMDB_DAY		0
#define PLMDB_MONTH	1
#define PLMDB_IMP		2
#define PLMDB_LDAY         3
#define PLMDB_LMONTH    4
#define PLMDB_LIMP         5

#define MAX_RUNSTATE 	8

#define MAX_PLMET_FENUM	4
#define MAX_PLMET_ENENUM	(MAX_PLMET_FENUM+1)

#define IMP_PLMET_FREZ		3

#define LINEWASTER_MAGIC   		0x761212f2
#define LINEWASTER_SAVE_PATH 	DATA_PATH

#define READMETERR_MAGIC  		0x761212f3
#define READMETERR_SAVE_PATH 	DATA_PATH
#define ITEMDNUM 				1 //��ȡ���������



typedef struct {
	unsigned char addr;   	//�����
	unsigned char runstate[MAX_RUNSTATE];  //״̬��
} mdbcur_t;  //��ǰ��
extern mdbcur_t  MdbCurData[MAX_METER+1];


typedef struct {
	unsigned short metnum1;
	unsigned short metnum2;
} plmdb_savehead_t;


//����ʧ�ܸ澯
typedef struct{
	unsigned char failcount;
}ReadMetErr_Alarm;


void LockPlMdb(void);
void UnlockPlMdb(void);

void SavePlMdb(void);


int MdbSaveMetAlarm(void);

#endif /*_PLMDB_H*/

