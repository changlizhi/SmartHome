/**
* alarm.h -- �¼��澯�ӿ�
* 
* ����: yangzhilong
* ����ʱ��: 2009-10-26
* ����޸�ʱ��: 2009-10-26
*/

#ifndef _ALARM_H
#define _ALARM_H

#define MAX_ALARM			1024

typedef struct {
	utime_t 	starttime;   	// ������ʼʱ�� 
	utime_t 	endtime;   		// ���Ž���ʱ�� 
	unsigned short palyedid;  	//�澯����
} alarm_buf_t;
extern alarm_buf_t AlarmCache[MAX_ALARM];


#ifndef  TRUE
#define  TRUE   1
#endif

#ifndef  FALSE
#define  FALSE  0
#endif

#ifndef BOOL
#define BOOL  int
#endif


void ClearAlarm();
int ActiveSendAlarm(unsigned char *sendbuffer);


#endif

