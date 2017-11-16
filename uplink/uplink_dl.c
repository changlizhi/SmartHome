/**
* uplink_dl.c -- ����ͨ��������·��
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-18
* ����޸�ʱ��: 2009-5-18
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "include/basetype.h"
#include "include/debug.h"
#include "include/lib/datachg.h"
#include "include/sys/schedule.h"
#include "include/lib/align.h"
#include "include/param/term.h"
#include "include/param/unique.h"
#include "uplink_pkt.h"
#include "uplink_dl.h"
#include "include/lib/datachg.h"
#include "svrcomm/faal.h"
#include "svrcomm.h"


unsigned short gPktLen = 0;//����֡���� 

static struct uplink_timer_t {
	int cnt;  //��ǰֵ
	int max;//��ʱ���
	int flag; //��Ч���
} UplinkTimer[UPLINKITF_NUM];

static struct uplink_fsm_t {
	unsigned char *pbuf;
	unsigned short cnt;
	unsigned short maxlen;
	unsigned char stat;
} UplinkFsm[UPLINKITF_NUM];


/**
* @brief �����ݰ���ʽ��Ϊ����ͨ�Ÿ�ʽ
* @param itf �ӿڱ��
* @param pkt ���ݰ�ָ��
* @return �ɹ��������ݰ�����, ʧ�ܷ���-1
*/
static int MakePacketG(unsigned char itf, uplink_pkt_tG *pkt)//ֻ��У��ͣ���Ĳ�����
{
	unsigned char strDataLen[2] ;
	unsigned short crc = 0;
	strDataLen[0] = pkt->len[0];
	strDataLen[1] = pkt->len[1];
	
	//int dataLen = *(unsigned short*)strDataLen; //ȥdata[]��ʵ��ռ�ó���	
	unsigned short dataLen = makepkt_short(strDataLen);
	int nLen = 10 +dataLen+ 2 +1;//��֡����= ֡ͷ+�����峤��+CRC+������
	crc = GetCRC16(pkt,nLen - 3);

	pkt->data[dataLen] = crc>>8;
	pkt->data[dataLen+1] = crc;
	pkt->data[dataLen+2] = 0x16;
	PrintHexLog(0,&pkt->head,nLen);
	return (nLen);
}

/**
* @brief ���ý��ն�ʱ��
* @param itf �ӿڱ��
* @param max ��ʱʱ��(100ms)
*/
static void SetUpTimer(unsigned char itf, int max)
{
	UplinkTimer[itf].cnt = 0;
	UplinkTimer[itf].max = max;
	UplinkTimer[itf].flag = 1;
}

/**
* @brief ֹͣ��ʱ��
*/
static void StopUpTimer(unsigned char itf)
{
	UplinkTimer[itf].flag = 0;
}

/**
* @brief �������״̬
* @param itf �ӿڱ��
*/
void UplinkClearState(unsigned char itf)
{
	UplinkFsm[itf].pbuf = UPLINK_RCVBUF(itf);
	UplinkFsm[itf].stat = 0;
	UplinkFsm[itf].cnt = 0;
	UplinkFsm[itf].maxlen = 0;

	StopUpTimer(itf);
}

/**
* @brief ���ն�ʱ������
*/
static void UpTimerProc(unsigned char itf)
{
	if(!UplinkTimer[itf].flag) {
		UplinkFsm[itf].pbuf = UPLINK_RCVBUF(itf);
		UplinkFsm[itf].stat = 0;
		UplinkFsm[itf].cnt = 0;
		UplinkFsm[itf].maxlen = 0;
		return;
	}

	UplinkTimer[itf].cnt++;
	if(UplinkTimer[itf].cnt >= UplinkTimer[itf].max) {
		UplinkClearState(itf);
	}

	return;
}


/*
*@brief У��ͼ��
*@param P ��ҪУ������ݵ��׵�ַ
*@param Len ��ҪУ��ĳ���
*/
char  CalcCheckSumB(char* P, unsigned short Len)
{
	char ret=0;
	unsigned short nInx = 0;
	for ( nInx=0; nInx<Len; nInx++)
	{
		ret += P[nInx];
	}
	return ret;
}

/*
brief:��鱨���е��ն˵�ַ�Ƿ��Ǳ�����ַ
para:pkt-����ָ��
return:0-�Ǳ�����ַ1-������ַ
*/
static inline int IsHostAddr(uplink_pkt_tG *pkt)
{
	PrintLog(0, "������ַ:");

	return 1;
}

/*
*@brief У��֡
*@param strStream ֡�׵�ַ
*@param Packlen  ֡����
*@����1��ʾ��ȷ������0 ��ʾ����
*/
int CheckStreamOK(unsigned char* strStream, int PackLen)
{
	uplink_pkt_tG	*pkt = (uplink_pkt_tG	*)strStream;
//	unsigned char   check = 0;
//	unsigned char   check2 = 0;
	unsigned short crc;
	unsigned short crc2;
	if ( (strStream[0]) != UPLINK_HEAD ) return 0;
	if ( (strStream[6]) != UPLINK_HEAD ) return 0;
	if ( strStream[PackLen-1]  != UPLINK_TAIL ) return 0;
	
	crc = GetCRC16((unsigned char *)strStream,PackLen - 3);
	crc2	= strStream[PackLen-3]<<8;
	crc2	|= strStream[PackLen-2];
	if(crc != crc2) return 0;
	return 1;
#if 0
	char nCheckSum = CalcCheckSumB((char *)strStream,PackLen - 2);
	check2 = nCheckSum&0xff;
	check = strStream[PackLen-2];
	PrintLog(0, "%02x,%02x,%d,%02x,%02x\n",nCheckSum&0xff,strStream[PackLen-2],PackLen,check,check2); 
	
	if (check2 != check) return 0;

	PrintLog(0, "rcv pkt!\n"); 
	/*by ydl modify 2010-08-24�ȼ�鱨���Ƿ񷢸�����*/
	if (IsHostAddr(pkt))
	{
		PrintLog(0, "�����Ƿ���������!\n");
		return 1;
	}
	else 
	{
		PrintLog(0, "���Ĳ��Ƿ���������!\n");
		return 0;
	}
#endif

}
/**
* @brief ����һ��ͨ��֡
* @param itf �ӿڱ��
* @param pkt ͨ��ָ֡��
* @return �ɹ�����0, ����ʧ��
*/
int UplinkSendPktG(unsigned char itf, uplink_pkt_tG *pkt)
{
      /*�˺���ֻ�ڷ���֮ǰ���������Ÿ�ֵ*/
	int len;
	int i=0;
	for(i=0;i<4;i++)
	{
		pkt->addr[i] = ParaTermG.deviceid[i*2]<<4 | ParaTermG.deviceid[i*2+1];
	}
	len = MakePacketG(itf, pkt);

	// if(UPLINK_NEEDPRINT(itf))
	 	faal_printpkt((faalpkt_t *)pkt, "SEND:");
	 if((*UplinkInterface[itf].rawsend)((unsigned char *)pkt, len)) 
	 {	
		return 1;
	}
	   return 0;
}

/**
* @brief ����һ��ͨ��֡
* @param itf �ӿڱ��
* @param pkt ͨ��ָ֡��
* @return �ɹ�����0, ����ʧ��
*/
int UplinkSendPktGAll(unsigned char itf, uplink_pkt_tG *pkt)
{
      /*�˺���ֻ�ڷ���֮ǰ���������Ÿ�ֵ*/
	int len,nItf;
	int i=0;
	for(i=0;i<4;i++)
	{
		pkt->addr[i] = ParaTermG.deviceid[i*2]<<4 | ParaTermG.deviceid[i*2+1];
	}

       len = MakePacketG(itf, pkt);

	for(nItf = 0;nItf<UPLINKITF_NUM;nItf++)
	{
	  if(UPLINK_NEEDPRINT(itf))faal_printpkt((faalpkt_t *)pkt, "SEND:");
	   if((*UplinkInterface[nItf].rawsend)((unsigned char *)pkt, len)) 
	   {	
		 continue;
	    }
	}
	   return 0;
}

/**
* @brief ��������֡(100ms����һ��)
* @param itf �ӿڱ��
* @return ����0  ��ʾ���յ�һ����ȷ��֡, ����1��ʾû��
*/
int UplinkRecvPkt(unsigned char itf)
{
	struct uplink_fsm_t *fsm = &UplinkFsm[itf];
	const uplinkitf_t *pitf = &UplinkInterface[itf];

	unsigned char *pktG;
	unsigned char uc; 
	UpTimerProc(itf);
	unsigned char strDataLen[2];
//	unsigned short dataLen;
	while( !(*pitf->getchar)(&uc) ) 
	{
		/*test:�����ڵ���*/
		#if 0
		if (itf == UPLINKITF_SERIAL)
		{
			PrintLog(0, "ser:%02x\r\n", uc);
		}
		#endif
		PrintLog(0, "fsm->stat:%d,%x \n",fsm->stat, uc);
		//if(uc == 0x16) PrintLog(0, "\n");
		switch(fsm->stat) {
		case 0:
			if(UPLINK_HEAD == uc) 				
			{	
				//�ҵ�֡ͷ
				UplinkClearState(itf);
				*(fsm->pbuf)++ = uc;
				fsm->cnt++;
				fsm->stat = 1;
				fsm->maxlen = 6;//ͬһ֡����0x68֮�����6���ֽ�
				SetUpTimer(itf, pitf->timeout);
			}	
			break;

		case 1:
			*(fsm->pbuf)++ = uc;
			fsm->cnt++;
			if(fsm->cnt >= fsm->maxlen) 
			{
			   	fsm->stat = 2;//�ӵ�����0x68
			   	fsm->maxlen = 10;
			}
			break;
                    
		case 2://����      
			if(UPLINK_HEAD != uc) 
			{
				UplinkClearState(itf);
				break;
			}
			*(fsm->pbuf)++ = uc;
                    fsm->cnt++;
			fsm->stat = 3;
			break;
		case 3:
			*(fsm->pbuf)++ = uc;
                     fsm->cnt++;
					 
		       if(fsm->cnt >= fsm->maxlen)
		       {
			   	fsm->stat = 4;//�ӵ�����������ݳ��Ⱥ󣬽�������׶η���
                       	
			  	strDataLen[0] = *(fsm->pbuf-2);
			 	strDataLen[1] = *(fsm->pbuf-1);
				//dataLen = *(unsigned short*)strDataLen;
				//DebugPrint(LOGTYPE_UPLINK, "fsm->stat: %d , strDataLen[0]:%0x, strDataLen[1]:%0x, dataLen=%d,make_short(strDataLen)=%d\n",fsm->stat,strDataLen[0],strDataLen[1],dataLen,make_short(strDataLen));
			  	unsigned short dataLen = makepkt_short(strDataLen);
                        	fsm->maxlen = dataLen+10+2;//��һ������Ҫ��ȡ�ĳ���
			}
			break;

		case 4://����DATA�ĵ�һ�ֽ�
			*(fsm->pbuf)++ = uc;
			fsm->cnt++;
			//DebugPrint(LOGTYPE_UPLINK, "fsm->stat: %d , %0x, %d,%\n",fsm->stat,uc,fsm->maxlen);
			if(fsm->cnt >= fsm->maxlen) 
				fsm->stat = 5;
			break;

		case 5:
			DebugPrint(LOGTYPE_UPLINK, "itf : %d,%x\n",itf,uc);
			if(UPLINK_TAIL != uc) {
				UplinkClearState(itf);
				break;
			}
			*(fsm->pbuf)++ = uc;
                    fsm->cnt++;
			StopUpTimer(itf);
			
		       pktG = (unsigned char *)UPLINK_RCVBUF(itf);//תΪ֡
			
			faal_printpkt((faalpkt_t *)pktG, "RECV:");   
		       if(CheckStreamOK(( unsigned char*)pktG,(int)fsm->cnt))//��ȷ
		       {
		       	//if(UPLINK_NEEDPRINT(itf)) 
					faal_printpkt((faalpkt_t *)pktG, "RECV:");

		         	UplinkClearState(itf);
				return 0;
		       }
			else
		     	{
		     	DebugPrint(LOGTYPE_UPLINK, "CheckStreamOK error\n");
			  	UplinkClearState(itf);	

		      	}
			break;

		default:
			UplinkClearState(itf);
			break;
		
	}
		}
       
	return 1;
}


/**
* @brief ��ȡ��ʱʱ����ط�����
* @param ptime ��ʱʱ��ָ��(100ms)
* @param retry �ط�����ָ��
*/
static void inline GetTimeout(int *ptime, int *retry)
{
	int i;
	i = (int)ParaUniG.snd_timeout;
	*ptime = i*10;
	*retry = (int)ParaUniG.snd_retry&0xff;
}

/**
* @brief �ж��Ƿ�Ϊ����Ҫ����ı��ģ�������������¼
* @pkt ͨ��ָ֡��
* @return �ǻ�Ӧ���ķ���1, ���򷵻�0
*/
 int IsEchoPkt(uplink_pkt_tG *pkt,unsigned char sndcmd)
{

	sndcmd &= FAALMASK_CMD;

	if(FAALCMD_ECHO_LOGON== sndcmd)
	{
		if(FAALCMD_ECHO_LOGON == pkt->cmd) return 1;
		else return 0;
	}
	else if(FAALCMD_ECHO_HBTEST == sndcmd)
	{
		if(FAALCMD_ECHO_HBTEST == pkt->cmd) return 1;
		else return 0;
	}	
	else if(FAALCMD_LOGONOUT == sndcmd)
	{
		if(FAALCMD_ECHO_HBTEST == pkt->cmd) return 1;
		else return 0;
	}

	return 0;
	
}

/**
* @brief ���ͱ��Ĳ��ȴ���Ӧ
* @param itf �ӿڱ��
* @param pkt ͨ��ָ֡��
* @return �ɹ�����0,���򷵻ش������
*/
static int UplinkSendWait(unsigned char itf, uplink_pkt_tG *psnd)
{
	int i, j;
	int times, retry;

	uplinkitf_t *pitf = (uplinkitf_t*)&UplinkInterface[itf];
	uplink_pkt_tG  *prcv = (uplink_pkt_tG*)UPLINK_RCVBUF(itf);

	GetTimeout(&times, &retry);//ֻ��һ��,����������ͳɹ���15������վ����ȷ�ϣ����ж�Ϊ��ʱ

	for(i=0; i<retry; i++) 
	{
		if(!(*pitf->linestat)()) return UPRTN_FAIL;

		if(UplinkSendPktG(itf, psnd)) 
		{
			   DebugPrint(0, "UplinkSendPktG error\n");
			   return UPRTN_FAIL;
		}
		
		for(j=0; j<times; j++) 
		{
			if(!UplinkRecvPkt(itf)) 
			{
				DebugPrint(LOGTYPE_UPLINK, "recvpak\n");
				if(!IsEchoPkt(prcv,psnd->cmd)) 
				{
					return UPRTN_OKRCV;
				}
				else 
				{
					return UPRTN_OK;
				}
			}

			Sleep(10);
		}
	}

	DebugPrint(LOGTYPE_UPLINK, "recvpak timeout!\n");
	return UPRTN_TIMEOUT;     
}

/**
* @brief ������������
* @param itf �ӿڱ��
* @param flag ���ͱ�־, 0-���ȴ���Ӧ, 1-�ȴ���Ӧ
* @return �ɹ�����0,���򷵻ش������
*/
int UplinkActiveSend(unsigned char itf, unsigned char flag, uplink_pkt_tG *psnd)
{     
	static unsigned char fseq = 1;
    if(!flag)
	 	return UplinkSendPktG(itf, psnd);
	 else
	 	return UplinkSendWait(itf, psnd);
}

/**
* @brief ��½��������
* @param itf �ӿڱ��
* @return �ɹ�����0,����ʧ��
*/
int UplinkLogon(unsigned char itf)
{
	  int rtn,i;
	  unsigned char *puc;
	  uplink_pkt_tG* pkt = (uplink_pkt_tG *)UPLINK_SNDBUF(itf);
	  pkt->ver = 0x01;
	  pkt->cmd = FAALCMD_LOGON;
	  FAAL_SETLEN(pkt, 0x4);
	  puc = pkt->data;
	  for(i=0; i<4; i++) puc[i] = ParaTermG.com_pwd[i];

	  pkt->head = 0x68;
      pkt->dep = 0x68;
	  pkt->cmd = 0xa1;	  

	  FAAL_SETLEN(pkt,4);
	  rtn = UplinkActiveSend( itf,1, pkt);
	  if(rtn){
	  	PrintLog(0,"logon fail!\r\n");
		return 1;
	  }
	  else{
		  	PrintLog(0,"logon ok!\r\n");
			return 0;
	  }
}

/**
* @brief ��½�˳�������
* @param itf �ӿڱ��
* @return �ɹ�����0,����ʧ��
*/
int UplinkLogonOut(unsigned char itf)
{
	  int rtn,i;
	  unsigned char *puc;
	  uplink_pkt_tG* pkt = (uplink_pkt_tG *)UPLINK_SNDBUF(itf);
	  pkt->ver = 0x01;
	  pkt->head = 0x68;
      pkt->dep = 0x68;
	  pkt->cmd = 0xa2;	  

	  FAAL_SETLEN(pkt,0);
	  rtn = UplinkActiveSend( itf,1, pkt);
	  if(rtn){
	  	PrintLog(0,"logon out fail!\r\n");
		return 1;
	  }
	  else{
		  	PrintLog(0,"logon out ok!\r\n");
			return 0;
	  }
}

/**
* @brief ��·���,������������
* @param itf �ӿڱ��
* @return �ɹ�����0,���򷵻ش������
*/
int UplinkLinkTest(unsigned char itf)
{

	uplink_pkt_tG *pkt = (uplink_pkt_tG *)UPLINK_SNDBUF(itf);	
    pkt->head = 0x68;
	pkt->ver = 0x01;
	pkt->dep= 0x68;
	pkt->cmd = 0xA4;//������
	FAAL_SETLEN(pkt,0);
	int rtn = UplinkActiveSend(itf, 1, pkt);//���������Ҫ��վ��Ӧ��֡
	if(UPRTN_FAIL == rtn || UPRTN_TIMEOUT== rtn) {
		PrintLog(0, "link test fail\r\n");
	}
	else if(UPRTN_OK == rtn) {
		PrintLog(0, "link test ok.\r\n");
	}

	return(rtn);
}
/**
* @brief �豸�������汾��
* @param itf �ӿڱ��
* @return �ɹ�����0,���򷵻ش������
*/

int UplinkCheckVer(unsigned char itf)
{
	
	uplink_pkt_tG *pkt = (uplink_pkt_tG *)UPLINK_SNDBUF(itf);	
	pkt->head = 0x68;
	pkt->ver = 0x01;
	pkt->dep= 0x68;
	pkt->cmd = 0x84;//������
	FAAL_SETLEN(pkt,0);
	int rtn = UplinkActiveSend(itf, 0, pkt);
	if(UPRTN_FAIL == rtn || UPRTN_TIMEOUT== rtn) {
			PrintLog(0, "link test fail\r\n");
	}
	else if(UPRTN_OK == rtn) {
			PrintLog(0, "link test ok.\r\n");
	}
	
	return(rtn);
}

/**
* @brief �����豸У�鱨��
* @param itf �ӿڱ��
* @return �ɹ�����0,���򷵻ش������
*/

int UplinkDeviceCheck(unsigned char itf)
{
	unsigned char *puc;
	
	int i;
	int filestat = 0;
	uplink_pkt_tG *pkt = (uplink_pkt_tG *)UPLINK_SNDBUF(itf);	
	pkt->head = 0x68;
	pkt->ver = 0x01;
	pkt->dep= 0x68;
	pkt->cmd = 0x81;//������
	FAAL_SETLEN(pkt, 0x1);
	puc = pkt->data;
	filestat = getFileDays();	//�ж���Ƶ�Ļ�״̬
	// 0X08������Ƶ���������У�0X0FΪ��ƵʱЧ�ѵ������ƽ�����
	if(filestat == 0)	//��Ƶ�ļ�δ����
		puc[0] = 0x08;
	else //��Ƶ�ļ�����
	{
		puc[0] = 0x0F;
	}
	
	int rtn = UplinkActiveSend(itf, 0, pkt);
	if(UPRTN_FAIL == rtn || UPRTN_TIMEOUT== rtn) {
			PrintLog(0, "link test fail\r\n");
	}
	else if(UPRTN_OK == rtn) {
			PrintLog(0, "link test ok.\r\n");
	}
	
	return(rtn);
}



