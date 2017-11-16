
/**
* datause.h -- ֧���������ò���ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-8
* ����޸�ʱ��: 2009-5-8
*/

#ifndef _PARAM_SCENEUSE_H
#define _PARAM_SCENEUSE_H

//�龰�������� (���ն�֧�ֵ�����������)
#define MAX_SCENECLASS	16  	//����龰��
#define MAX_METNUM  	32  	//һ���龰���֧�ֵı���

typedef struct __attribute__((packed)){
//typedef struct {
	unsigned char  attr;  			//��������
	unsigned short metid;			//����ID
	unsigned char  state[8];  		//����״̬
} cfg_datafns_t;

typedef struct __attribute__((packed)){
//typedef struct {
	unsigned char id;				//�龰���(���趨��ŵ���������������±��+1)
	unsigned char num;				//���Ƶ��豸����
	char 		     scene_name[16];		//�龰����
	cfg_datafns_t met[MAX_METNUM];
} cfg_scenecls_data_t;

typedef struct __attribute__((packed)){
//typedef struct {
	unsigned short  flag;	//�龰������0xFFFF
	cfg_scenecls_data_t scenecls[MAX_SCENECLASS];  //�龰	
} para_sceneuse_t;

#ifndef DEFINE_PARASCENEUSE
extern  para_sceneuse_t ParaSceneUse;
#define ParaSceneUseCls(sceneclass)	(ParaSceneUse.scenecls[sceneclass])
#endif

extern const cfg_scenecls_data_t  AllCloseCls;	//ȫ��
extern const cfg_scenecls_data_t  AllOpenCls; //ȫ��

int SaveParaSceneUse(void);
int SaveParaTimerTask(void);
#define MAX_TIMERTASK	10  	//���ʱ������
#define MAX_ACTION  	32  	//�����������������

typedef struct {
	unsigned char 	id;						//������(���趨��ŵ���������������±��+1)
	unsigned char 	num;					//���ƵĶ�������
	char 		     	task_name[16];			//��������
	char				hour;					//Сʱ
	char				min;					//����
	char				weekflag;				//���ڱ�־
	char				bStart;					//�Ƿ�����
	cfg_datafns_t 		met[MAX_ACTION];
} cfg_timertaskcls_data_t;

extern  cfg_timertaskcls_data_t ParaTimerTask[MAX_TIMERTASK];

#endif /*_PARAM_SCENEUSE_H*/

