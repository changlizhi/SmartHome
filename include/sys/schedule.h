#ifndef _SCHEDULE_H
#define _SCHEDULE_H

#include <unistd.h>

/**
* @brief ����˯��һ��ʱ��
* @param ticks -- ˯�ߵ��¼�, ��10msΪ��λ
*/
#define Sleep(ticks)    usleep((unsigned long)(ticks)*10000)

#endif /*_SCHEDULE_H*/
