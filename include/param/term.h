
/**
* term.h -- �ն˲���ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-6
* ����޸�ʱ��: 2009-5-6
*/

#ifndef _PARAM_TERM_H
#define _PARAM_TERM_H

#include "capconf.h"
#include "../version.h"

typedef struct {
	//unsigned char uplink;   			//����ͨ�Žӿ�
	unsigned char unuse[3];

	//unsigned char addr_mac[6];  	//�ն�MAC��ַ

	//char manuno[14];  	   		//�ն��ⲿ�������
	//char manuno_inner[12];  		//�ն��ڲ��������
} para_manuf_t;

#ifndef DEFINE_PARAMANUF
para_manuf_t ParaManuf;
#endif


#define SVRADDR_TYPE_GPRS			2  // GPRS/CDMA
#define SVRADDR_TYPE_PSTN			3  // PSTN
#define SVRADDR_TYPE_ETHER		4  // ��̫��
#define SVRADDR_TYPE_RS232		6  // RS232/485
#define SVRADDR_TYPE_CSD			7  // CSD
#define SVRADDR_TYPE_RADIO		8  // ����
#define SVRADDR_TYPE_SMSWAKE		9  // ���Ż���
#define SVRADDR_TYPE_ADSL			20  // ADSL

#define MAX_CAMERA_NUM			4
#define MAX_CAMERA_CHANEL_NUM	2
//����ȼ�
#define PASSWD_HIGH		2
#define PASSWD_LOW            	1
#define PASSWD_READONLY   	0
#define PASSWD_ERROR      	-1

#define AUTLEVEL_HIGH        	2
#define AUTLEVEL_LOW         	1
#define AUTLEVEL_OTHER      	0
#define AUTLEVEL_ERROR     	-1

extern int PasswdLevel;
extern int Autlevel;

typedef union {
	struct {
		unsigned char chn;  //ͨ������
		unsigned char uc[8];
	} mix;

	struct //__attribute__((packed)){
	{
		unsigned char chn;  //ͨ������
		unsigned char unused; //���ֽ����
		unsigned char unused2;  //����ַ�
              unsigned char ip[4];  //IP
		unsigned short port;  //�˿ں�	
	} net;

	struct {
		unsigned char chn;  //ͨ������
		unsigned char phone[8];
	} pstn;
	#define channel mix.chn
} cfg_svraddr_tG;




typedef struct __attribute__((packed)){
//typedef struct{	
	unsigned char 	index;			//������
	unsigned char		nchanel;		//ͨ����
	unsigned char		fac_type;		//���̴���,1Ϊ��������,2Ϊ�ǰ�	
	unsigned short 	net_port;		//����˿ں�
	char 			net_addr[32];	//�����ַ
	char				username[16];	//��¼�û���	
	char				password[16];	//��¼����	
	char				videoname[16];
}Camera;

//typedef struct __attribute__((packed)){
typedef struct{	
	unsigned char 	autoflag;				//ע���־1Ϊ��ע��,0Ϊδע��
	char				register_code[13];		//ע����	
}RegisterInfo;

typedef struct{
	unsigned short maxtolMeter;//8811
	unsigned short maxplcmet;  //8812
	unsigned short maxcenmet; //8813
	unsigned char  maximpmet; //8814
}MaxMeter_tG;

// �˿�1~4 4·RS485,
#define RS485_PORTNUMPORT    3   //���485�˿���Ŀ
#define PORTCFG_NUM    7//UPLINKITF_NUM//8   //���˿ڲ�����Ŀ
typedef struct __attribute__((packed)){
//typedef struct{
	unsigned char valid;    //��Ч��־
	unsigned char baud;   //������, 
	unsigned char parity;
	unsigned char databits;
	unsigned char stopbits;
	unsigned char func;	    //�˿ڹ���//0,����1����2����
} portcfg_t;

typedef struct {
	cfg_svraddr_tG svraddr;  //8010 ��վͨѶ��ַ
	cfg_svraddr_tG svraddr_1;  //8011 ������վͨѶ��ַ1
	cfg_svraddr_tG svraddr_2;  //8012 ������վͨѶ��ַ1
	unsigned char sms_addr[16];  //8013 �������ĺ���
	cfg_svraddr_tG gate_addr;  //8014 Ĭ�����ص�ַ
	char apn[16];  //8015 APN
	char  MusicState;			//��Ƶ�ļ�״̬ 0--��Ч�������С�1--��Ƶ�Ѿ����ڡ�2--��Ƶ�����ڡ�3--
	unsigned char deviceid[8];
	unsigned short ledscreenPort; //LED��ʾ���˿�
	char strledscreenaddr[16];	  //LED��ʾ����ַ
	char strmusicpwd[16];
	unsigned short music_volume;  //������С
	unsigned char  first_start;  //�״�����
	unsigned char  Musicmonth;
	unsigned char login_update_system;
	unsigned char login_down_musice;
	char cdma_usr[32];  //8019CDMA��½�û���//��ŵ��ַ�������ֱ��ʹ�ã���cmnet
	char cdma_pwd[32];  //801ACDMA��½�û���//ͬ��

	unsigned char nor_pwd[3];   //8020 ��ͨ����(ֻ��Ȩ��)
	unsigned char com_pwd[4];  //8021 �������� (Ȩ�޵�)
	unsigned char adm_pwd[3];  //8022 ����Ա����   (  Ȩ�޸�)	

	unsigned char search_device;  //8810 �������
	unsigned char task_starthour;  //8815 ��ʱ������ʼʱ��
	unsigned char task_startdev;  //8816 ��ʱ����ִ�м��
	                              //(00H:30���� 01H:60����(Ĭ��) 02H:120����
	                              //03H:240���� 04H:360���� 05H:720����)
	unsigned char plc_route_type;  //8817 �ز��м̷�ʽ(00:�Զ��м� ����:�̶��м�)
	unsigned char gate_linewaste[2];  //8818 �����ʱ�����ֵ(0.1%)
	unsigned char hour_upimpdata;  //8819 �ص㻧�����ϴ�ʱ��(ʱ0~23, ΪFF�Ǳ�ʾ�������ϱ���Ĭ��ΪFF)
	unsigned char hour_updaydata;  //881A �ն��������ϴ�ʱ��(ʱ0~23, ΪFF�Ǳ�ʾ�������ϱ���Ĭ��ΪFF)
	unsigned int   alarm_flag;  //881B �澯ʹ�ܿ�����
	                           //D7=1����������ֵ/��ֵ����
	                           //D6=1����ʧѹ����
	                           //D5=1����ʧ������
	                           //D4=1�����������澯
	                           //D3=1�������̸澯
	                           //D2=1������ʧ�ܸ澯
	                           //D1=1������ʱ���쳣�澯
	                           //D0=1����ͣ���¼��澯
	                           //����Ԥ��

	unsigned char cascade_addr[16];  //881D �������ն˵�ַ�б�(4��, ĳ��ַ����FFFFFFFFʱ��ʾ������)
	unsigned char cascade_flag;  //881E ������/����ն˼�����־(ֻʹ��D2,D1,D0λ,����λ��0; 
	                             //D2=1����ʾ������; D1=1����ʾ��������; D0=1����ʾ���ն�Ϊ���ն�)
	unsigned char day_read_mondata;  //8820 ��ĩ���ݳ��տ�ʼʱ��(��, 1~28)
	unsigned char hour_read_mondata;  //8820 ��ĩ���ݳ��տ�ʼʱ��(ʱ, 0~23)

	unsigned char day_up_mondata;  //8821 ��ĩ�����ϴ���ʼʱ��(��, 1~28)
	unsigned char hour_up_mondata;  //8821 ��ĩ�����ϴ���ʼʱ��(ʱ, 0~23)

	unsigned char peibian_addr[4];	//8822:̨����Ӧ����ַ���Զ����������
	unsigned char device_code[16];
	MaxMeter_tG  stmaxmeter; //�������ͱ�����
	unsigned char ct[2]; //̨���Ӧ���CT
	RegisterInfo    reg;
	
	
	Camera   	camerainfo[MAX_CAMERA_NUM];
	
	portcfg_t port[PORTCFG_NUM];   //87xx, �˿�����
}para_term_tG; //���Э��

#ifndef DEFINE_PARATERM
extern para_term_tG ParaTermG;
#endif

//int CheckDataLenFromDio(unsigned short dio);
int  AlterTermPara(unsigned short dio, char *pData, int nLen, unsigned short nTn);
int  TermPara8010(char *pstr,cfg_svraddr_tG* pcf);
int  BuffRev(char* pstr,  int nLen);
int  ReadTermPara(unsigned short  dio, char *res);
//int LoadParaManuf(void);
int SaveParaTerm(void);
int  MakeDeviceCode();
void  GetDeviceCode(unsigned char *deviceid,int *autoflag);
//int SaveParaManuf(void);

//ע������汾��ΪCCXX-AIT-FFF-NNNNN ��ʽ��CC ��ʾ���̴��루BCD �룩��XX ��ʾ��ͬ���͵������
//A ���汾��I �ΰ汾��T С�汾��FFF ������Ϣ��NNNNNN �����������ʾ�ط�������Ϣ��
inline static void maketermversion(unsigned char* buf, int buflen)
{
/*
	if(buflen<8)  return ;
	
	buf[0] = 0x01;
	buf[1] = VERSION_PROJECT;
	buf[2] = ((VERSION_MAJOR<<4)&0xf0) | (VERSION_MINOR&0x0f);
	buf[3] = 0;
	buf[4] = 0;
	buf[5] = 0x80;
	buf[6] = 0x41;
	buf[7] = 0;
	*/
}
#endif

