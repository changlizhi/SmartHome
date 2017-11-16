/**
* keepalive.c -- �����������������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-19
* ����޸�ʱ��: 2009-5-19
*/

#include <stdio.h>
#include <string.h>

#include "include/basetype.h"
#include "include/debug.h"
#include "include/sys/timeal.h"
#include "include/param/term.h"
#include "uplink_pkt.h"
#include "svrcomm.h"
#include "keepalive.h"
#include "include/param/unique.h"
/**
* @brief ��ȡ��������
* @return ��������(100ms)
*/

static int GetCycKeepAlive(void)
{
      int i 	 = 10*60*ParaUniG.keepalive_cyc   ;//keepalive_cyc��λΪ����,Ĭ����15����
	return(i);
}

#define TIMEOUT_KEEPALIVE    600    // 1 minute
#define TIMEOUT_GNOWAIT    600    // 1 minute
typedef struct {
	int cnt;
	int cnt_max;
	int cnt_getcyc;
	int cnt_retry;
} keepalive_stat_t;
static keepalive_stat_t keepalive_stat;

/**
* @brief ���״̬
*/
void ClearKeepAlive(void)
{
     int cyc = GetCycKeepAlive();//crt����

	 keepalive_stat.cnt = 0;
	keepalive_stat.cnt_retry = 0;
	keepalive_stat.cnt_getcyc = 0;
	keepalive_stat.cnt_max = cyc;
}

/**
* @brief ����Ƿ��ڿ�����ʱ��
* @return �����߷���1, �������߷���0
*/
int KeepAliveInPeriod(void)
{
#if 0
#define TIMOUT_CHECK	600  // 1minute
	static int lastrtn = 1;
	static int count = TIMOUT_CHECK;

	if(ParaUniG.clientmode != 2) return 1;

	count++;
	if(count > TIMOUT_CHECK) {
		sysclock_t clock;
		unsigned int mask;

		count = 0;
		SysClockReadCurrent(&clock);
		mask = (unsigned int)1<<(clock.hour);
		//if(mask&ParaTerm.uplink.onlineflag) lastrtn = 1;
		//else lastrtn = 0;
	}

	return lastrtn;
#endif
	return 1;
}

/**
* @brief �������Ӵ���
* @return ����0-��Ҫ������·���Ի��ߵ�½, 1-��Ҫ������·
*/
#if 0
int KeepAliveProc(void)
{
	keepalive_stat.cnt++;
	if(keepalive_stat.cnt > keepalive_stat.cnt_max)
       	return 0;
	if(LINESTAT_ON != SvrCommLineState)  //add by crt
		return 0;//
	return 1;
}
#else

/**
* @brief �������Ӵ���
* @return ����0-��Ҫ������·���Ի��ߵ�½, 1-��Ҫ������·
*/
int KeepAliveProc(void)
{
	int cnt_maxretry = (int)ParaUniG.keepalive_sndretry& 0xff;

	if(cnt_maxretry == 0) cnt_maxretry = 3;

	if((LINESTAT_OFF == SvrCommLineState) && (keepalive_stat.cnt_max > 1800)
		&& (keepalive_stat.cnt_retry < cnt_maxretry))
	{
		int cnt_timedail = (int)ParaUniG.keepalive_dialtime&0xff;// 
	
		cnt_timedail *= 10;
		if(cnt_timedail == 0) cnt_timedail = 600;
		keepalive_stat.cnt++;
		if(keepalive_stat.cnt > cnt_timedail) {
			keepalive_stat.cnt = 0;
			keepalive_stat.cnt_getcyc = 0;
			keepalive_stat.cnt_max = GetCycKeepAlive();
			return 0;
		}
	}
	else if(keepalive_stat.cnt_max >= 100) {
		keepalive_stat.cnt++;
		if(keepalive_stat.cnt > keepalive_stat.cnt_max) {
			keepalive_stat.cnt = 0;
			keepalive_stat.cnt_getcyc = 0;
			keepalive_stat.cnt_max = GetCycKeepAlive();
			return 0;
		}
	}
	else {
		keepalive_stat.cnt_getcyc++;
		if(keepalive_stat.cnt_getcyc > TIMEOUT_KEEPALIVE) {
			keepalive_stat.cnt_getcyc = 0;
			keepalive_stat.cnt_max = GetCycKeepAlive();
			return 0;
		}
	}

	return 1;
}

#endif
extern int svrcomm_havetask(void);

/**
* @brief ˢ����·����
* @return �ɹ�0, ����ʧ��
*/
int RefreshKeepAlive(void)
{
	
	if((LINESTAT_ON == SvrCommLineState) && 
		(keepalive_stat.cnt >= TIMEOUT_GNOWAIT) 
		&& (svrcomm_havetask()))
	{
		keepalive_stat.cnt = 0;
		keepalive_stat.cnt_getcyc = 0;
		keepalive_stat.cnt_max = GetCycKeepAlive();
		return 0;
	}

	return 1;
}

/**
* @brief ���ñ�־
* @param flag ��־
*/
void SetKeepAlive(unsigned char flag)
{
	switch(flag) {
	case KEEPALIVE_FLAG_LOGONFAIL:
		//keepalive_stat.cnt_retry++;
		break;

	case KEEPALIVE_FLAG_LOGONOK:
		keepalive_stat.cnt_retry = 0;
		break;
	/*by ydl add 2011-05-13*/
	case KEEPALIVE_FLAG_TIMEOUT:
		keepalive_stat.cnt = keepalive_stat.cnt_max + 1;
		break;	
	/*end*/	

	default: break;
	}
}

