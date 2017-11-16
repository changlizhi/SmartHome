/**
* cyssave.h -- ���ڴ���
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-6-11
* ����޸�ʱ��: 2009-6-11
*/

#ifndef _CYCSAVE_H
#define _CYCSAVE_H

#define CYCSAVE_FLAG_RESET   0x00000001  //���ڸ�λǰ����

struct cycle_save {
	void (*pfunc)(void);
	unsigned int flag;
};

/**
* @brief ����һ�����ڴ���
* @param func ִ�к���
* @param flag Ϊ0��ʾ��������ִ��, ΪCYCSAVE_FLAG_RESET��ʾ���ڸ�λǰ����
*/
#define DECLARE_CYCLE_SAVE(func, flag) \
	static const struct cycle_save _cycsave_##func \
	__attribute__((__used__)) \
	__attribute__((section("_cycle_save"), unused)) \
	= {func, flag}

/**
* @brief ѭ������
* @param flag 0-��������, 1-��λǰ����
*/
void SysCycleSave(int flag);

#endif /*_CYCSAVE_H*/

