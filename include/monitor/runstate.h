#ifndef _RUNSTATE_H
#define _RUNSTATE_H

typedef struct {
	unsigned char flag;// 1����������0û����������
	unsigned char ver[8];
}softchg_stat_t;

typedef struct {
	softchg_stat_t softchg; 	//�汾���

	struct {
		unsigned short head;    	//ѭ����ͷ����
		unsigned short cur;  		//ѭ����β����
		unsigned short snd;  		//������������
		unsigned char  playstate;	//0--�޲��� 1--���ڲ���
	} alarm;  //�澯�ļ�״̬
	unsigned char cnt_snderr; //�澯�ط�������	
	unsigned char alarmtime;//ʱ�Ӹ澯ÿ��ֻ�ж�һ�θ澯1:�ж�,0δ�ж�
} runstate_tG;

#ifndef DEFINE_RUNSTATE
extern runstate_tG RunStateG;
#endif

/**
* @brief ����޸�����״ָ̬��
* @return ������ָ��
*/
runstate_tG *RunStateModifyG(void);


/**
* @brief ��������״̬
*/
void SaveRunState(void);
void ClearRunState(void);
#endif /*_RUNSTATE_H*/

