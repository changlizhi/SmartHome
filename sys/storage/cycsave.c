/**
* cyssave.c -- ���ڴ���
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-6-11
* ����޸�ʱ��: 2009-6-11
*/

#include <stdio.h>
#include "include/sys/cycsave.h"

static void DummyFunc(void)
{
	//printf("cycle save dummy func\n");
	return;
}
DECLARE_CYCLE_SAVE(DummyFunc, 0);

extern const struct cycle_save __start__cycle_save[];
extern const struct cycle_save __stop__cycle_save[];

/**
* @brief ѭ������
* @param flag 0-��������, 1-��λǰ����
*/
void SysCycleSave(int flag)
{
	unsigned int i;

	for(i=0; __start__cycle_save+i<__stop__cycle_save; i++) 
	{
		if(__start__cycle_save[i].flag & CYCSAVE_FLAG_RESET) {
			if(flag) (__start__cycle_save[i].pfunc)();
		}
		else (__start__cycle_save[i].pfunc)();
	}
}

