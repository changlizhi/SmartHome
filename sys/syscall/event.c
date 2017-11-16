/**
* event.c -- �¼��ӿ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2008-5-16
* ����޸�ʱ��: 2009-3-30
*/

#include <pthread.h>

#include "include/sys/event.h"

/**
* @brief ��ʼ���¼����Ʊ���
* @param pctrl �¼����Ʊ���ָ��
*/
void SysInitEvent(sys_event_t *pctrl)
{
	pthread_mutex_init(&pctrl->mutex, NULL);
	pthread_cond_init(&pctrl->cond, NULL);
	pctrl->event = 0;
}

/**
* @brief �ȴ��¼�
* @param pctrl �¼����Ʊ���ָ��
* @param bwait �ȴ�ʱ�Ƿ����, 
*          ���Ϊ0, �򲻹���û���յ�����յ��¼�, ��������ֱ�ӷ���
*          ���Ϊ1, �����û���յ�����յ��¼�, ���񽫹���, ֱ���յ�
* @param waitmask ��Ҫ�ȴ����¼�
* @param pevent ���յ����¼�
*/
void SysWaitEvent(sys_event_t *pctrl, int bwait, unsigned long waitmask, unsigned long *pevent)
{
	unsigned long ul;

	pthread_mutex_lock(&pctrl->mutex);

	ul = pctrl->event;

	if(!bwait) 
	{
		if(ul&waitmask) 
		{
			ul &= waitmask;
			pctrl->event &= ~waitmask;
		}
		else ul = 0;
	}
	else 
	{
		while(1) 
		{
			if(ul&waitmask) 
			{
				ul &= waitmask;
				pctrl->event &= ~waitmask;
				break;
			}

			pthread_cond_wait(&pctrl->cond, &pctrl->mutex);
			ul = pctrl->event;
		}
	}

	pthread_mutex_unlock(&pctrl->mutex);

	*pevent = ul;
}

/**
* @brief �����¼�
* @param pctrl �¼����Ʊ���ָ��
* @param event ��Ҫ���͵��¼�
*/
void SysSendEvent(sys_event_t *pctrl, unsigned long event)
{
	pthread_mutex_lock(&pctrl->mutex);
	pctrl->event |= event;
	pthread_cond_signal(&pctrl->cond);
	pthread_mutex_unlock(&pctrl->mutex);
}
