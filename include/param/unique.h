/**
* unique.h -- �Զ������
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-18
* ����޸�ʱ��: 2009-5-18
*/
#ifndef _PARA_UNIQUE_H
#define _PARA_UNIQUE_H

#include "commport.h"

typedef struct __attribute__((packed)){
//typedef struct {
	unsigned char autogetip;//�Ƿ��Զ���ȡIP��ַ
	unsigned char ipterm[4];//IP��ַ
	unsigned char maskterm[4];//����
	unsigned char ipgatew[4];//����
	unsigned char ipproxy[4];//����
	unsigned char mac[6];     //mac��ַ��
	unsigned short portproxy;//����˿�
	unsigned char proxy_type;//��������
	unsigned char proxy_connect;//���ӷ�ʽ
	char username[32];//�û�����
	char pwd[32];//����
	char mobile1[12];		//���Ž��պ���1
	char mobile2[12];		//���Ž��պ���2
	char mobile3[12];
	char email[32];	//���ո澯�������ַ
	unsigned short portlisten;//UDP֡���˿�
} cfg_termip_tG;

//typedef struct __attribute__((packed)){
typedef struct {
	char username[32];//�û�����
	char pwd[32];//����
	unsigned char isopensms;	//�������ű�������0Ϊ�ر�,1Ϊ����
	char smsmobile1[12];		//���Ž��պ���1
	char smsmobile2[12];		//���Ž��պ���2
	char smsmobile3[12];		//���Ž��պ���3
	unsigned char isopenemail;	//�����ʼ�����������0Ϊ�ر�,1Ϊ����
	char recvemail[32];		//���ո澯�������ַ
	char emailsender[32];		//163�����ַ
	char emailpwd[32];		//163��������
} cfg_userinfo_tG;
//������������
typedef struct{
	int cascaMode; //����ģʽ0   ��ģʽ 1 ��ģʽ
	cfg_para_485port_t para_485port;
	char cascade_addr[4];	//��Ϊ���ն�ʱ���ն˵�ַ
}cfg_cascade_tG;

//�๦�ܱ����
typedef struct{
	cfg_para_485port_t para_485port;
	char usrname[6];//ͨ���û���
	char passwd[6];//ͨ������
}cfg_MetConfig_tG;
typedef struct {
	unsigned short start_time;  //hour*60+minute
	unsigned short end_time;
}period_time_t;

typedef struct {
	period_time_t period_time[8];
}cfg_termperiod_t;

typedef struct {
	unsigned char read_period[12];  	//������ʱ��(ȱʡΪ0)
	unsigned char cenmet_fenum;		//�ܱ������(0~4��ȱʡΪ0)
	unsigned char siphmet_fenum; 		//����������(0~4��ȱʡΪ0)
	unsigned char muphmet_fenum; 	//���׶๦�ܱ������(0~4��ȱʡΪ0)
	unsigned char watermet_fenum; 	//ˮ�������(0~4��ȱʡΪ0)
	unsigned char gasmet_fenum; 		//���������(0~4��ȱʡΪ0)
	unsigned char daytomonth;  		//0-��Ч��1-��ÿ��1���ն��ᵱΪ�¶������ݣ�2-���¶������ݵ�Ϊ�����ն������ݣ�ȱʡΪ0
	unsigned char chktimeday[4];  		//D0~D30�ֱ��ʾÿ��1��~31�ţ���1��ʾ��ʱ��0��ʾ����ʱ��ȱʡΪ04 00 00 00����ÿ��3�Ž�ʱ
	unsigned char keepalive_cyc;  		//��������(����), ȱʡΪ15����
	unsigned char snd_timeout;  		//���ͳ�ʱ(��), ȱʡΪ30��
	unsigned char snd_retry;  			//�ط�������ȱʡΪ2
	unsigned char proto_cenmet;  		//�ܱ�ͨѶ��Լ
	unsigned char clientmode;  			//0-��������, 1-��������, 2-ʱ������
	unsigned char timedown;             	//��ͨ���Զ�����ʱ�� minute

	unsigned char addr_mac[6];  //�ն�MAC��ַ
	
	cfg_termip_tG  	termip;   			//������ip��ַ�Ͷ˿�
	cfg_userinfo_tG 	userinfo;				//�û���Ϣ
	cfg_cascade_tG cascade_term; 		//�����ն˵�ַ
	cfg_MetConfig_tG metConfig;		//�๦�ܱ�ͨѶ����
	cfg_para_485port_t para_485bus;    	//485����
	
	unsigned char linewasterhour;

	char xccode[8];//���̱���
	char drcode[8];//�������
	char dxcode[8];//���ű���
	char rskcode[8];//��˹������
	char lkcode[8];//�ʽ����
	char kncode[8];//���ܱ���
	
	unsigned char autojudge;//�Ƿ��Զ��ж�·�ɵ����ز�è����1:�Զ�ʶ��0:�ֶ�����
	unsigned char autoStudy;//�Զ�ѧϰ���  1 �Զ�ѧϰ 0 �ֶ�ѧϰ Ĭ��Ϊ�ֶ�ѧϰ

	char manuno[14];  	   		//�ն��ⲿ�������
	char manuno_inner[12];  		//�ն��ڲ��������
	unsigned char keepalive_sndretry;/*���ʹ���*/
	unsigned char keepalive_dialtime;/*�ؼ��ʱ��*/
	unsigned short itemid1;/*���ڵ��д������(0x9010,0x9090)*/
	unsigned short itemid2;
	//���д�������
	unsigned char serial_databits;//���Դ�������λ
	unsigned char serial_stopbits;//���Դ���ֹͣλ
	char serial_checkbit;//���Դ���У��λ
	unsigned int serial_baud;//���Դ�������
	unsigned char poll_time;//������ѯ
	unsigned char serialtoird;//������ά���ڻ���:2Ϊ���Դ���,0Ϊ����,1Ϊά������
	unsigned char downlink;//����ͨ�ŷ�ʽ--������ʽ
	unsigned char metmon_dev;//485����ʱ��
	unsigned char itemnum;//�ز��Զ������������
	unsigned char checktimeday;//Уʱ��һ��
	unsigned char checktimehour;//УʱСʱ
	unsigned char pflag; //0:��Ч 1:��Ч
	unsigned char prdcount;//ʱ����
	cfg_termperiod_t period;    //����ʱ��added by yzl.2010.6.24
	unsigned char cassflag; //���ܱ������ն�ʱ��ѡ��(�����ʼ���:0�ܱ�,1����ն�)
	unsigned char checktime;//Уʱ��ʱʱ��
	
} para_uni_tG;

#ifndef DEFINE_PARAUNI
extern para_uni_tG ParaUniG;
#endif

int SaveParaUni(void);

#endif 

