/**
* mutex.c -- �����������ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2008-5-16
* ����޸�ʱ��: 2009-4-23
*/

#ifndef _SYS_MUTEX_H
#define _SYS_MUTEX_H

#include <unistd.h>
#include <pthread.h>

///������Ʊ�������
#define sys_mutex_t 		pthread_mutex_t

/**
* @brief ��ʼ��������Ʊ���
* @param p ������Ʊ���ָ��
*/
#define SysInitMutex(p)		pthread_mutex_init(p, NULL)

/**
* @brief ��ס������Ʊ���
*     ����ñ���û�б���, ����ס�ñ���
*     ����ñ�������, ���������, ֱ����ס�����������ͷ�
* @param p ������Ʊ���ָ��
*/
#define SysLockMutex(p)		pthread_mutex_lock(p)

/**
* @brief �ͷŻ�����Ʊ���
* @param p ������Ʊ���ָ��
*/
#define SysUnlockMutex(p)	pthread_mutex_unlock(p)

#if 0  /*Ŀǰ�汾pthread��֧�ֶ�д��*/
///��д�����Ʊ�������
#define sys_rwlock_t		pthread_rwlock_t

/**
* @brief ��ʼ����д�����Ʊ���
* @param p ��д�����Ʊ���ָ��
*/
#define SysInitRwLock(p)	pthread_rwlock_init(p, NULL)

/**
* @brief ������д��(�Զ�ΪĿ��)
* @param p ��д�����Ʊ���ָ��
*/
#define SysReadLockRwLock(p)	pthread_rwlock_rdlock(p)

/**
* @brief ������д��(��дΪĿ��)
* @param p ��д�����Ʊ���ָ��
*/
#define SysWriteLockRwLock(p)	pthread_rwlock_wrlock(p)

/**
* @brief ������д��
* @param p ��д�����Ʊ���ָ��
*/
#define SysUnLockRwLock(p)		pthread_rwlock_unlock(p)
#else
#endif

#endif /*_SYS_MUTEX_H*/

