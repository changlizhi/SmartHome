/**
* timer.c -- ��ʱ�������ӿ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2008-5-16
* ����޸�ʱ��: 2009-6-6
*/

#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/ioctl.h>

#include "include/basetype.h"
#include "sys/sys_config.h"
#include "include/sys/task.h"
#include "include/sys/schedule.h"
#include "include/sys/mutex.h"
#include "include/sys/timeal.h"
#include "include/sys/timer.h"
#include "include/debug.h"
#include "include/startarg.h"
#include "include/sys/gpio.h"
#include "include/debug/shellcmd.h"

//ʱ�Ӷ�ʱ�����Ʊ����ṹ
typedef struct st_rtman {
	struct st_rtman *next;
	struct st_rtman *prev;
	int id;
	rtimerproc_t proc;
	unsigned long arg;
	utime_t tstart;
	utime_t tbase;
	unsigned char dev;
	unsigned char mod;
	unsigned char bonce;
	unsigned char flag;
	utime_t basetime;
} rtman_t;

//��Զ�ʱ�����Ʊ����ṹ
typedef struct st_ctman {
	struct st_ctman *next;
	struct st_ctman *prev;
	int id;
	ctimerproc_t proc;
	unsigned long arg;
	unsigned long dev;
	unsigned long cnt;
	unsigned char flag;
} ctman_t;

static void CTimerProc(void);
static void RTimerProc(utime_t timec);

//����ִ������ָ��(200msִ��һ��)
static void (*FastRountine)(void) = NULL;
//ϵͳ�������������е�����
static int SysJiffies;

static int FeedWatchdog = 1;

/**
* @brief ʹ�ܻ��ֹι��
* @param flag 0-��ֹ, 1-ʹ��
*/
void EnableFeedWatchdog(int flag)
{
	FeedWatchdog = flag;
}

/**
* @brief ϵͳ��ʱ������
* @param arg ��������
*/
static void *SysTimerTask(void *arg)
{
	sysclock_t clock;
	int countRtimer;
	int bakJiffies;
	int fd;
	static char runflag = 0;

	SysClockRead(&clock);

	countRtimer = 0;

	while(1) {
		if(NULL != FastRountine) (*FastRountine)();

//		read(fd, (char *)&SysJiffies, sizeof(SysJiffies));
		if(SysJiffies != bakJiffies) {
			if(FeedWatchdog) write(fd, (char *)&clock, sizeof(clock));  //feed watchdog
			CTimerProc();
			bakJiffies = SysJiffies;
		}

		countRtimer++;
		if(countRtimer >= 4)  { // 0.8s
			countRtimer = 0;
			SysClockRead(&clock);
			RTimerProc(UTimeReadCurrent());

			runflag = (!runflag); 
			/*end*/
		}

		Sleep(20);
		if(exitflag)
			break;
	}

	return 0;
}

/**
* @brief ���ÿ�������
* @param routine ����������ں���
*/
void SysSetFastRoutine(void (*routine)(void))
{
	FastRountine = routine;
}

/**
* @brief ��ȡϵͳ��������������������
* @return ϵͳ��������������������
*/
int SysReadJiffies(void)
{
	return SysJiffies;
}

#define TMAN_EMPTY   0
#define TMAN_VALID   1

//ʱ�Ӷ�ʱ�����Ʊ�����
static rtman_t RTimerList;
static rtman_t RTimerBuffer[MAX_RTIMER];
//��Զ�ʱ�����Ʊ�����
static ctman_t CTimerList;
static ctman_t CTimerBuffer[MAX_CTIMER];
//ͬ����ʱ�����ʵĻ������
static sys_mutex_t CTimerMutex, RTimerMutex;
//����ID,������ֹID�ظ�
static int CTimerIdAddup = 0;
static int RTimerIdAddup = 0;

/**
* @brief ���һ�����Զ�ʱ��
* @param dev ��ʱ��ִ�м��(����Ϊ��λ)
* @param proc ��ʱ��������
* @param arg ��ʱ��������
*/
int SysAddCTimer(int dev, ctimerproc_t proc, unsigned long arg)
{
	int i;
	ctman_t *p;

	AssertLogReturn(dev<=0, -1, "invalid dev(%d)\n", dev);

	SysLockMutex(&CTimerMutex);

	for(i=0; i<MAX_CTIMER; i++) {
		if(TMAN_EMPTY == CTimerBuffer[i].flag) {
			p = &(CTimerBuffer[i]);
			p->flag = TMAN_VALID;
			p->proc = proc;
			p->arg = arg;
			p->cnt = 0;
			p->dev = dev;
			p->id = (CTimerIdAddup & 0xffff) | (i << 16);
			CTimerIdAddup++;

			p->next = &CTimerList;
			p->prev = CTimerList.prev;
			CTimerList.prev->next = &CTimerBuffer[i];
			CTimerList.prev = &CTimerBuffer[i];

			SysUnlockMutex(&CTimerMutex);
			return p->id;
		}
	}

	SysUnlockMutex(&CTimerMutex);

	ErrorLog("CTimer full\n");
	return -1;
}

/**
* @brief ֹͣ��Զ�ʱ��
* @param id ��ʱ��id
*/
void SysStopCTimer(int id)
{
	ctman_t *p;
	int offset;

	offset = id>>16;
	if((offset < 0) || (offset >= MAX_CTIMER)) {
		ErrorLog("invalid id(%d)\n", id);
		return;
	}

	p = &CTimerBuffer[offset];

	SysLockMutex(&CTimerMutex);

	if((p->id == id) && (TMAN_EMPTY != p->flag)) {
		p->flag = TMAN_EMPTY;
		p->prev->next = p->next;
		p->next->prev = p->prev;
	}

	SysUnlockMutex(&CTimerMutex);
}

/**
* @brief ֹͣ��Զ�ʱ��(ָ����ʽ)
* @param p ��ʱ�����Ʊ���ָ��
*/
static void StopCTimerP(ctman_t *p)
{
	if(TMAN_EMPTY != p->flag) {
		p->flag = TMAN_EMPTY;
		p->prev->next = p->next;
		p->next->prev = p->prev;
	}
}

/**
* @brief �����Զ�ʱ��������,���¿�ʼ����
* @param id ��ʱ��id
*/
void SysClearCTimer(int id)
{
	ctman_t *p;
	int offset;

	offset = id>>16;
	if((offset < 0) || (offset >= MAX_CTIMER)) {
		ErrorLog("invalid id(%d)\n", id);
		return;
	}

	p = &CTimerBuffer[offset];

	SysLockMutex(&CTimerMutex);

	if((p->id == id) && (TMAN_EMPTY != p->flag)) {
		p->cnt = 0;
	}

	SysUnlockMutex(&CTimerMutex);
}

/**
* @brief ��Զ�ʱ��������
*/
static void CTimerProc(void)
{
	ctimerproc_t func;
	ctman_t *p, *p1;
	int rc;

	SysLockMutex(&CTimerMutex);

	p = CTimerList.next;
	while(p != &CTimerList) {
		p1 = p->next;

		p->cnt++;
		if(p->cnt >= p->dev) {
			p->cnt = 0;
			func = p->proc;
			rc = (*func)(p->arg);
			if(rc) StopCTimerP(p);
		}

		p = p1;
	}

	SysUnlockMutex(&CTimerMutex);
}

/**
* @brief �������ü����׼ʱ��
* @param p ʱ�Ӷ�ʱ�����Ʊ���ָ��
* @return ��׼ʱ��
*/
static utime_t RTimerGetBase(unsigned char mod, const sysclock_t *baseclock)
{
	utime_t rtn;
	sysclock_t clock;

	memcpy(&clock, baseclock, sizeof(clock));

	clock.year = clock.month = 0;
	switch(mod) {
	case UTIMEDEV_MINUTE:
		//clock.minute = 0;
	case UTIMEDEV_HOUR:
		clock.hour = 0;
	case UTIMEDEV_DAY:
		clock.day = 0;
		break;
	default: //month
		if(clock.day) clock.day -= 1;
		break;
	}

	rtn = 0;
	if(0 != clock.day) rtn += ((utime_t)(clock.day)&0xff)*1440*60;
	if(0 != clock.hour) rtn += ((utime_t)(clock.hour)&0xff)*60*60;
	if(0 != clock.minute) rtn += ((utime_t)(clock.minute)&0xff)*60;

	return rtn;
}

/**
* @brief ���¼��㶨ʱ������ʱ��
* @param p ʱ�Ӷ�ʱ�����Ʊ���ָ��
* @param curtime ��ǰʱ��
*/
static void RecalRTimerP(rtman_t *p, utime_t curtime)
{
	sysclock_t clock;

	if(UTIMEDEV_MINUTE == p->dev) {
		if(0 == p->mod) p->dev = 15;
		else p->dev = 1;
	}
	if(p->mod > UTIMEDEV_MONTH) p->mod = UTIMEDEV_HOUR;

	if(p->bonce) return;

	UTimeToSysClock(curtime, &clock);

	switch(p->mod) {
	case UTIMEDEV_MONTH:
		clock.month = 1;
	case UTIMEDEV_DAY:
		clock.day = 1;
	case UTIMEDEV_HOUR:
		clock.hour = 0;
	case UTIMEDEV_MINUTE:
		clock.minute = 0;
		clock.second = 0;
		break;
	default:
		return;
	}

	p->tstart = SysClockToUTime(&clock);
	p->tbase = p->tstart;
	//p->tstart += RTimerGetBase(p);
	p->tstart += p->basetime;
	while(curtime >= p->tstart) {
		p->tbase = UTimeAdd(p->tbase, p->mod, p->dev);
		p->tstart = p->tbase + p->basetime;
		//p->tstart += RTimerGetBase(p);
		//p->tstart += p->basetime;
	}

	//DebugPrint(LOGTYPE_SHORT, "rtimer start: %s\n", UTimeFormat(p->tstart));

	//PrintLog(0,"rcal timer: %s\n", ascii_utime(p->tstart));
	//print_utime(p->tstart, "recal rtimer");
}

/**
* @brief ���¼���ʱ�Ӷ�ʱ��
* @param id ��ʱ��id
*/
void SysRecalRTimer(int id)
{
	rtman_t *p;
	int offset;

	offset = id>>16;
	if((offset < 0) || (offset >= MAX_RTIMER)) return;

	p = &RTimerBuffer[offset];

	SysLockMutex(&RTimerMutex);

	if((p->id == id) && (TMAN_EMPTY != p->flag)) {
		RecalRTimerP(p, UTimeReadCurrent());
	}

	SysUnlockMutex(&RTimerMutex);
}

/**
* @brief ���¼�������ʱ�Ӷ�ʱ��
*/
void SysRecalAllRTimer(void)
{
	rtman_t *p;

	DebugPrint(LOGTYPE_ALARM, "recall all rtimer...\n");

	SysLockMutex(&RTimerMutex);

	p = RTimerList.next;
	while(p != &RTimerList) {
		if(TMAN_EMPTY != p->flag) {
			RecalRTimerP(p, UTimeReadCurrent());
		}

		p = p->next;
	}

	SysUnlockMutex(&RTimerMutex);
}

/**
* @brief ���һ�����ʱ�Ӷ�ʱ��
* @param pconfig ��ʱ�������ñ���ָ��
* @param proc ��ʱ��������
* @param arg ����������
* @return �ɹ�ʱ���ض�ʱ��id, ���򷵻�-1
*/
int SysAddRTimer(const rtimer_conf_t *pconf, rtimerproc_t proc, unsigned long arg)
{
	int i;
	rtman_t *p;

	if((0 == pconf->tdev) || (pconf->tmod > UTIMEDEV_MONTH)) {
		ErrorLog("invalid conf(%d, %d)\n", pconf->tdev, pconf->tmod);
		return -1;
	}

	//print_logo(0, "add rtimer: %d, %d\r\n", pconf->tdev, pconf->tmod);

	SysLockMutex(&RTimerMutex);

	for(i=0; i<MAX_RTIMER; i++) {
		if(TMAN_EMPTY == RTimerBuffer[i].flag) {
			p = &(RTimerBuffer[i]);
			p->flag = TMAN_VALID;
			p->proc = proc;
			p->arg = arg;
			p->bonce = pconf->bonce;
			if(pconf->bonce) {
				p->dev = 1;
				p->mod = 1;
				p->tstart = pconf->curtime;
			}
			else {
				p->dev = pconf->tdev;
				p->mod = pconf->tmod;
				//p->basetime = pconf->basetime;
				p->basetime = RTimerGetBase(pconf->tmod, &pconf->basetime);
				RecalRTimerP(p, pconf->curtime);
			}
			p->id = (RTimerIdAddup & 0xffff) | (i << 16);
			RTimerIdAddup++;

			p->next = &RTimerList;
			p->prev = RTimerList.prev;
			RTimerList.prev->next = &RTimerBuffer[i];
			RTimerList.prev = &RTimerBuffer[i];

			SysUnlockMutex(&RTimerMutex);
			return p->id;
		}
	}

	SysUnlockMutex(&RTimerMutex);

	ErrorLog("RTimer full\n");
	return -1;
}

/**
* @brief ֹͣһ��ʱ�Ӷ�ʱ��
* @param id ��ʱ��id
*/
void SysStopRTimer(int id)
{
	rtman_t *p;
	int offset;

	offset = id>>16;
	if((offset < 0) || (offset >= MAX_RTIMER)) return;

	p = &RTimerBuffer[offset];

	SysLockMutex(&RTimerMutex);

	if((p->id == id) && (TMAN_EMPTY != p->flag)) {
		p->flag = TMAN_EMPTY;
		p->prev->next = p->next;
		p->next->prev = p->prev;
	}

	SysUnlockMutex(&RTimerMutex);
}

/**
* @brief ֹͣһ��ʱ�Ӷ�ʱ��(ָ����ʽ)
* @param p ʱ�Ӷ�ʱ�����Ʊ���ָ��
*/
static void StopRTimerP(rtman_t *p)
{
	if(TMAN_EMPTY == p->flag) return;

	p->flag = TMAN_EMPTY;
	p->prev->next = p->next;
	p->next->prev = p->prev;
}

/**
* @brief ʱ�Ӷ�ʱ��������
* @param timec ��ǰʱ��
*/
static void RTimerProc(utime_t timec)
{
	rtimerproc_t func;
	rtman_t *p, *p1;
	int bstart;
	int comp;

	SysLockMutex(&RTimerMutex);

	p = RTimerList.next;
	while(p != &RTimerList) {
		p1 = p->next;
		bstart = 0;

		if(timec >= p->tstart) {
			bstart = 1;
			if(!(p->bonce)) {
				comp = timec - p->tstart;
				if(comp > 3600) {   //�Ӻ�ִ�д���һСʱ���¼���
					RecalRTimerP(p, timec);
				}
				else {
					do {
						p->tbase = UTimeAdd(p->tbase, p->mod, p->dev);
						p->tstart = p->tbase + p->basetime;
						//p->tstart += RTimerGetBase(p);
					} while(timec >= p->tstart);
				}
			}
		}

		if(bstart) {
			func = p->proc;

			(*func)(p->arg, timec);

			if(p->bonce) StopRTimerP(p);
		}

		p = p1;
	}

	SysUnlockMutex(&RTimerMutex);
}

/**
* @brief ��ʱ��ģ���ʼ������
* @return ����0��ʾ�ɹ�, ����ʧ��
*/
DECLARE_INIT_FUNC(SysTimerInit);
int SysTimerInit(void)
{
	int i, arg;
	sysclock_t clock;
	extclock_t extclock;

	for(i=0; i<MAX_RTIMER; i++) RTimerBuffer[i].flag = TMAN_EMPTY;
	RTimerList.next = RTimerList.prev = &RTimerList;

	for(i=0; i<MAX_CTIMER; i++) CTimerBuffer[i].flag = TMAN_EMPTY;
	CTimerList.next = CTimerList.prev = &CTimerList;

	SysInitMutex(&CTimerMutex);
	SysInitMutex(&RTimerMutex);

	if(!GetStartArg('d', NULL, 0)) arg = 1; //��ι��, ������
	else arg = 0;

	if(ExtClockRead(&extclock)) {
	
		return 1;
	}
	clock.year = extclock.year;
	clock.month = extclock.month;
	clock.day = extclock.day;
	clock.hour = extclock.hour;
	clock.minute = extclock.minute;
	clock.second = extclock.second;
	SysClockSet(&clock);

	SysCreateTask(SysTimerTask, (void *)arg);

	SET_INIT_FLAG(SysTimerInit);

	return 0;
}

int shell_timerinfo(int argc, char *argv[])
{
	char flag;

	if(2 != argc) {
		PrintLog(0, "timerinfo r/c\n");
		return 1;
	}

	flag = argv[1][0];

	if('c' == flag) {
		ctman_t *p;

		p = CTimerList.next;
		while(p != &CTimerList) {

			PrintLog(0, "ctimer %2d: ", ((unsigned int)p-(unsigned int)CTimerBuffer)/sizeof(ctman_t));
			PrintLog(0, "dev=%ds, count=%d\n", p->dev, p->cnt);

			p = p->next;
		}
	}
	else if('r' == flag) {
		rtman_t *p;

		p = RTimerList.next;
		while(p != &RTimerList) {

			PrintLog(0, "rtimer %2d: ", ((unsigned int)p-(unsigned int)RTimerBuffer)/sizeof(rtman_t));
			PrintLog(0, "dev=%d, mod=%d, once=%d\n", p->dev, p->mod, p->bonce);
			PrintLog(0, "  base=%s, ", UTimeFormat(p->basetime));
			PrintLog(0, "start=%s\n", UTimeFormat(p->tstart));

			p = p->next;
		}
	}
	else {
		PrintLog(0, "invalid arg\n");
		return 1;
	}

	PrintLog(0, "end\n");
	return 0;
}
DECLARE_SHELL_CMD("timerinfo",shell_timerinfo, "��ʾϵͳ��ʱ����Ϣ");

