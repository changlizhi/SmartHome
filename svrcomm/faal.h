#ifndef _FAAL_H
#define _FAAL_H

#define LEN_FAAL_HEAD    10
#define LEN_FAAL_RDTNHD    8
#define LEN_FAAL_HEAD_CHK		4

#define FAAL_HEAD    0x68
#define FAAL_TAIL    0x16
#define FAAL_TAIL_MCHK 0x0d

#define FAALMASK_DIR     0x80
#define FAALMASK_ABNOR     0x40
#define FAALMASK_CMD    0x3f

#define FAALCMD_RDTNDATA    0x02
#define FAALCMD_ECHO_RDTN    0x81
#define FAAL_MASK_ISEQ    0xe0

#define FAALCMD_LOGON    0xa1
#define FAALCMD_ECHO_LOGON    0x21

#define FAALCMD_HBTEST    0xa4
#define FAALCMD_ECHO_HBTEST    0x24

#define FAALCMD_LOGONOUT    0xa2
#define FAALCMD_ECHO_LOGONOUT    0x22


#define FAALCMD_ECHO_LOGON    0x21


#define FAAL_GETLEN(pkt, alen)    (alen) = makepkt_short((pkt)->len)
#define FAAL_SETLEN(pkt, alen)    departpkt_short(alen, (pkt)->len)

/*�����붨��*/
#define FAALCMD_LOGIN    0x25
#define FAALCMD_ECHO_LOGIN    0xa5

//����
#define FAALCMD_HEARTBEAT   		0x23
#define FAALCMD_ECHO_HEARTBEAT    	0xa3

#define FAALCMD_RDTN    0x01

#define FAALCMD_WROBJ    0x08
#define FAALCMD_ECHO_WROBJ    0x88
typedef struct   __attribute__((packed)){
//typedef struct{
	unsigned short tn;
	unsigned char aut;
	unsigned char pw[3];
	unsigned char data[1];
} faal_wrobj_t;

#define FAALCMD_WRREALOBJ    0x07
#define FAALCMD_ECHO_WRREALOBJ    0x87
typedef struct __attribute__((packed)){
//typedef struct{
	//unsigned char tn;
	unsigned short tn;
	unsigned char aut;
	unsigned char pw[3];
	mntime_t time;
	unsigned char timeout;
	unsigned char data[1];
} faal_wrrealobj_t;

/*������Զ������,��ԭ��Э��ѹ�����0F(���Ź�����ʱ��ΪԶ������)*/
#define FAALCMD_SELFDEF    0x0f
#define FAALCMD_ECHO_SELFDEF    0x8f
#define FAAL_WINNUM_FILEDATA    32

/*������ʵʱ�ٲ�����*/
#define FAALCMD_REALRD 0x11
#define FAALCMD_ECHO_REALRD 0x91

/*��վ�ظ��豸��֤���*/
#define FAALCMD_SOFTWAREVER 		0x04
#define FAALCMD_ECHO_DEVICECHECK 	0x84

/*��վ�ظ��豸��֤���*/
#define FAALCMD_DEVICECHECK 		0x01
#define FAALCMD_ECHO_DEVICECHECK 	0x81


/*��վ�·�������Ƶ�ļ�*/
#define FAALCMD_UPDATEAUDIOSTR 		0x03
#define FAALCMD_ECHO_UPDATEAUDIOSTR 0x83


/*����LED��ʾ��*/
#define FAALCMD_SETLEDSTR 0x0E
#define FAALCMD_ECHO_SETLEDSTR 0x8E


/*�����������ճ��ۺ�����*/
#define FAALCMD_RDFDATA 0x12
#define FAALCMD_ECHO_RDFDATA 0x92


/*�����������ص��û���������*/
#define FAALCMD_RDMFDATA 0x13
#define FAALCMD_ECHO_RDMFDATA 0x93

/*�������Ե������բ����*/
#define FAALCMD_METRELAY 0x14
#define FAALCMD_ECHO_METRELAY 0x94

/*���ղ�������������*/
#define FAALCMD_SCENEON 0x16
#define FAALCMD_ECHO_SCENEON 0x96

/*��������:���ڼ������ɼ�����ն˵�������*/
#define FAALCMD_CASCADRD 0x17
#define FAALCMD_ECHO_CASCADRD 0x97

/*��������:����ʵ�����ն˶�ʱ��ѯ���ն��ϱ�����Ĺ���*/
#define FAALCMD_SCENEOFF 0x18
#define FAALCMD_ECHO_SCENEOFF 0x98

/*��ȡ�澯:*/
#define FAALCMD_QRYALM 0x09
#define FAALCMD_ECHO_QRYALM 0x89
typedef struct {
	unsigned char year;
	unsigned char month;
	unsigned char day;
	unsigned char hour;
	unsigned char min;	
	unsigned char num;
} faal_qryalm_t;
#define LEN_FAAL_SALMHD    1
typedef struct {
	unsigned char num;
	unsigned char data[1];
} faal_salmhd_t;
/*ȡ���ٲ�����*/
#define FAALCMD_CMDCANCEL 0x20
#define FAALCMD_ECHO_CMDCANCEL 0xa0

#define FAALCMD_CSD_GETDFREE 0x28

typedef struct __attribute__((packed)){
//typedef union{
	struct
	{
		unsigned char sele[2];
		unsigned char year;
		unsigned char mon;
		unsigned char day;
		unsigned char dat[1];
	}read;
	struct
	{
		unsigned char sele[2];
		unsigned char frame[1];
	}
	resnd;
}readfreedata_t;

/*���������յ����*/
#define FAALCMD_RDMINFO 0x15
#define FAALCMD_ECHO_RDMINFO 0x95
//typedef struct
typedef struct __attribute__((packed))
{
	unsigned short mid;
	unsigned short num;
}faal_rdminfo_t;

/*�����붨��*/
#define FAALERR_OK    0    /*��ȷ*/
#define FAALERR_FORWARDERR    1    /*�м�����û�з���*/
#define FAALERR_SETINVALID    2    /*�������ݷǷ�*/
#define FAALERR_PWERR    3    /*����Ȩ�޲���*/
#define FAALERR_NODATA    4    /*�޴�������*/
#define FAALERR_TIMEOUT    5    /*����ʱ��ʧЧ*/
#define FAALERR_NOADDR    0x11    /*Ŀ���ַ������*/
#define FAALERR_SNDERR    0x12    /*����ʧ��*/
#define FAALERR_SMSLONG    0x13    /*����Ϣ̫֡��*/

typedef struct {
	unsigned char city_no;
	unsigned char county_no;
	unsigned char sn[2];
} rtua_t;

typedef struct __attribute__((packed)){
//typedef struct{
	unsigned char head;  //=68H
	unsigned char ver;
	unsigned char addr[4];  //addr
	unsigned char dep;    //=68H
	unsigned char cmd;
	unsigned char len[2];
	unsigned char data[5];
} faalpkt_t;

typedef struct{
	unsigned char tnflag[8];
	unsigned char item[1];
} faal_rdtn_t;



#endif
