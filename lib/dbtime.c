/**
* dbtime.c -- ���ݿ�ʱ���ʽ
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-24
* ����޸�ʱ��: 2009-5-24
*/
#include "include/basetype.h"
#include "include/lib/dbtime.h"

static const unsigned char MonthMaxDays[] = {
	0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 0, 0, 0
};
#if 0
/**
* @brief ����1��
* @param pdbtime ���ݿ�ʱ�����ָ��
*/
void DbTimeAddOneDay(dbtime_t *pdbtime)
{
	unsigned maxdays;

	maxdays = MonthMaxDays[pdbtime->s.month];
	if(2 == pdbtime->s.month && 0 == (pdbtime->s.year&0x03)) maxdays += 1;

	pdbtime->s.day++;
	if(pdbtime->s.day > maxdays) {
		pdbtime->s.day = 1;
		pdbtime->s.month++;
		if(pdbtime->s.month > 12) {
			pdbtime->s.month = 1;
			pdbtime->s.year++;
		}
	}
}

/**
* @brief ����1��
* @param pdbtime ���ݿ�ʱ�����ָ��
*/
void DbTimeAddOneMonth(dbtime_t *pdbtime)
{
	pdbtime->s.month++;
	if(pdbtime->s.month > 12) {
		pdbtime->s.month = 1;
		pdbtime->s.year++;
	}
}
#endif
/**
* @brief ����1��
* @param pdbtime ���ݿ�ʱ�����ָ��
*/
void DbTimeAddOneDay(dbtime_t *pdbtime)
{
	unsigned maxdays;

	maxdays = MonthMaxDays[pdbtime->s.month];
	if(2 == pdbtime->s.month && 0 == (pdbtime->s.year&0x03)) maxdays += 1;

	pdbtime->s.day++;
	if(pdbtime->s.day > maxdays) {
		pdbtime->s.day = 1;
		pdbtime->s.month++;
		if(pdbtime->s.month > 12) {
			pdbtime->s.month = 1;
			pdbtime->s.year++;
		}
	}
}

/**
* @brief ����1��
* @param pdbtime ���ݿ�ʱ�����ָ��
*/
void DbTimeSubOneDay(dbtime_t *pdbtime)
{
	unsigned maxdays;

	pdbtime->s.day--;
	if(pdbtime->s.day == 0) {
		pdbtime->s.month--;
		if(pdbtime->s.month == 0) {
			pdbtime->s.month = 12;
			pdbtime->s.year--;
		}		
		
		maxdays = MonthMaxDays[pdbtime->s.month];
		if(2 == pdbtime->s.month && 0 == (pdbtime->s.year&0x03)) maxdays += 1;
		pdbtime->s.day = maxdays;
	}
}

/**
* @brief ����1��
* @param pdbtime ���ݿ�ʱ�����ָ��
*/
void DbTimeAddOneMonth(dbtime_t *pdbtime)
{
	pdbtime->s.month++;
	if(pdbtime->s.month > 12) {
		pdbtime->s.month = 1;
		pdbtime->s.year++;
	}
}

/**
* @brief ����1��
* @param pdbtime ���ݿ�ʱ�����ָ��
*/
void DbTimeSubOneMonth(dbtime_t *pdbtime)
{
	pdbtime->s.month--;
	if(pdbtime->s.month == 0) {
		pdbtime->s.month = 12;
		pdbtime->s.year--;
	}
}

/**
* @brief ����15����
* @param pdbtime ���ݿ�ʱ�����ָ��
*/
void DbTimeAddOneTick(dbtime_t *pdbtime)
{
	pdbtime->s.tick++;
	if(pdbtime->s.tick > 95) {
		pdbtime->s.tick = 0;
		DbTimeAddOneDay(pdbtime);
	}
}
