/**
* sqlitedb.c -- ��ini�ı������ļ�����ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-4-22
* ����޸�ʱ��: 2009-4-22
*/

#ifndef _SQLITEDB_H
#define _SQLITEDB_H

//��������ļ�
// param table_name : ����
// param pdata: ���뻺����
// param pdatalen 	: ����������
int ReadFromTable(char * table_name, unsigned char * pdata, unsigned int pdatalen);

//�������ļ�
// param table_name : ����
// param qdata: ���������
// param qdatalen 	: ����������
int SaveToTable(char * table_name, unsigned char * qdata, unsigned int qdatalen);
#endif /*_XIN_H*/

