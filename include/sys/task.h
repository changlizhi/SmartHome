/**
* event.h -- ����ӿ�ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-3-30
* ����޸�ʱ��: 2009-3-31
*/

#ifndef _SYS_TASK_H
#define _SYS_TASK_H

#include <unistd.h>

/**
* @brief ����һ������(�߳�)
* @param routine ������ʼִ�к���
* @param arg �ɹ�����0, ʧ�ܷ��ط���ֵ
*/
int SysCreateTask(void *(*routine)(void *), void *arg);

/**
* @brief �ȴ���������(�߳�)����,�����̵���
*/
void SysWaitTaskEnd(void);

#endif /*_SYS_TASK_H*/
