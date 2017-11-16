#include "include/basetype.h"
#include "itemop.h"
#include "para_term.h"
#include "include/param/capconf.h"
#include "include/param/term.h"
#include "include/param/sceneuse.h"
#include "include/debug.h"
#include "include/lib/datachg.h"
#include "include/sys/timeal.h"
#include "include/sys/timer.h"
#include "include/sys/gpio.h"
#include "include/version.h"
#include "include/param/unique.h"
#include "include/lib/bcd.h"
#include "include/lib/align.h"
#include "downlink/plcomm.h"
#include "downlink/plmdb.h"
#include "include/monitor/alarm.h"
#include "include/sys/schedule.h"
extern void SysRestart(void);
//�ı���վͨ���ŵ��踴λ
static int CTimerSysRestart(unsigned long arg)
{
	DebugPrint(0,"SysRestart\n");
	SysRestart();
	return 1;
}
static int CTimerSamplingData(unsigned long arg)
{
	PlcSamplingMetid = arg;
	return 1;
}
//�������,
//times ��Ĵ���
static int BeepSound(int times)
{
	int i = 0;
	for(i=0;i<times;i++)
	{
		system("echo 1 > /dev/buzzer");
		Sleep(100);
		system("echo 0 > /dev/buzzer");
		Sleep(50);
		system("killall -9 madplay");
	}
}

static int TimeSamplingId	 =-1;	//���ݲ�����ʱ��
/*
Func Description: ��վͨ�ŵ�ַ
Func Param:
	flag: 0-��, 1-д
	op: ��������ָ��
Func Return: ITORTN_*
*/

int paraterm_svraddr(unsigned char flag, itemop_t *op)
{
	cfg_svraddr_tG *paddr = (cfg_svraddr_tG *)&ParaTermG.svraddr;
	unsigned char *puc = op->buf;
	unsigned char oldchn;

	if (op->id == 0x8010)
	{
		paddr = (cfg_svraddr_tG *)&ParaTermG.svraddr;
	}
	else if (op->id == 0x8011)
	{
		paddr = (cfg_svraddr_tG *)&ParaTermG.svraddr_1;
	}
	else
	{
		paddr = (cfg_svraddr_tG *)&ParaTermG.svraddr_2;
	}

	if(0 == flag) //read
	{
		puc[8] = paddr->channel;
		hextobcd(&puc[8], 1);
		switch(paddr->channel)
		{
		case SVRADDR_GPRS:
		case SVRADDR_ETHERNET:
			depart_short(paddr->net.port, puc);
			puc += 2;
			memcpy(puc, paddr->net.ip, 4);
			BuffRev((char *)puc, 4);
			
			puc += 4;

			*puc++ = 0xaa;
			*puc++ = 0xaa;
			break;

		case SVRADDR_SMSWAKE:
			if(0x8010 == op->id)
			{
				depart_short(paddr->net.port, puc);
				puc += 2;
				
				memcpy(puc, paddr->net.ip, 4);
				BuffRev((char *)puc, 4);
				puc += 4;

				*puc++ = 0xaa;
				*puc++ = 0xaa;

				break;
			}

		default:
			BuffRev((char *)puc, 8);
			smallcpy(puc, paddr->pstn.phone, 8);
			break;
		}

//		PrintHexLog(0, (unsigned char *)paddr, 9);//test
		return 0;
	}
	else
	{
		bcdtohex(&puc[8], 1);

		oldchn = paddr->channel;
		switch(puc[8])
		{
		case SVRADDR_GPRS:
		case SVRADDR_ETHERNET:
			paddr->channel = puc[8];
			paddr->net.port = make_short(puc);

			BuffRev((char *)(&puc[2]), 4);
			memcpy(paddr->net.ip, &puc[2], 4);
			break;

		case SVRADDR_SMSWAKE:
			if(0x8010 == op->id)
			{
				paddr->channel = puc[8];
				paddr->net.port = make_short(puc);

				BuffRev((char *)(&puc[2]), 4);
				memcpy(paddr->net.ip, &puc[2], 4);
				break;
			}

		case SVRADDR_RS232:
		//case SVRADDR_SMS:
	//	case SVRADDR_485LINK:
		//case SVRADDR_METCHK:
			BuffRev((char *)puc, 8);
			smallcpy(paddr->pstn.phone, puc, 8);
			paddr->channel = puc[8];
			break;

		default:
			return ITORTN_OPFAIL;
		}

		if(0x8010 == op->id)
		{
			if(oldchn != paddr->channel) //chn changed
			{
				SysAddCTimer(5, CTimerSysRestart, 0);
			}
		}

//		PrintHexLog(0, (unsigned char *)paddr, 9);//test
		return 0;
	}
}

/*
Func Description: ���ص�ַ
Func Param:
	flag: 0-��, 1-д
	op: ��������ָ��
Func Return: ITORTN_*
*/
int paraterm_gateaddr(unsigned char flag, itemop_t *op)
{
	unsigned char *puc = op->buf;

	if(0 == flag)
	{
		depart_short(ParaTermG.gate_addr.net.port, puc);
		puc += 2;
		memcpy(puc, ParaTermG.gate_addr.net.ip, 4);
		BuffRev((char *)puc, 4);
		puc += 4;

		*puc++ = 0xaa;
		*puc++ = 0xaa;

		return 0;
	}
	else
	{
		ParaTermG.gate_addr.net.port = make_short(puc);
		puc += 2;
		BuffRev((char *)puc, 4);
		memcpy(ParaTermG.gate_addr.net.ip, puc, 4);
		
		/*if(FAALITF_ETHER == svrcomm_itf)
		{
			netop_t netop;

			netop.itf = NETOPITF_ETHER;
			netop.op = NETOP_SETGATEWAY;
			netop.arg.ipaddr.ip = htonl(para_term.gate_addr.net.ip);
			netop.arg.ipaddr.mask = 0;
			net_ioctl(&netop);
		}*/

		return 0;
	}
}

/*
Func Description: APN
Func Param:
	flag: 0-��, 1-д
	op: ��������ָ��
Func Return: ITORTN_*
*/
int paraterm_apn(unsigned char flag, itemop_t *op)
{
	int i, len;
	char *pstr;

	if(0 == flag)
	{
		for(len=0; len<16; len++)
		{
			if((ParaTermG.apn[len] == 0) || (ParaTermG.apn[len] == 0xaa))
				break;
		}
	
		pstr = (char *)op->buf;
		for(i=0; i<len; i++)
		{
			/*by ydl modify 2011-05-18*/
			op->buf[i] = ParaTermG.apn[len-1-i];
//			op->buf[i] = ParaTermG.apn[i];
		}
		for(i=len; i<16; i++)
		{	
			//op->buf[i] = 0xaa;
			op->buf[i] = 0x00;/*���������λ���������*/
		}
	}
	else
	{
		for(len=0; len<15; len++)
		{
			if((0xaa == op->buf[len]) || (0 == op->buf[len]))
				break;
		}

		for(i=0; i<len; i++)
		{
			/*by ydl modify 2011-05-18*/
			ParaTermG.apn[i] = op->buf[len-1-i];
//			ParaTermG.apn[i] = op->buf[i];
		}
		for(i=len; i<16; i++)
			ParaTermG.apn[i] = 0;
	}

	return 0;
}

/*
Func Description: �û���������
Func Param:
	flag: 0-��, 1-д
	op: ��������ָ��
Func Return: ITORTN_*
*/
int paraterm_usrname(unsigned char flag, itemop_t *op)
{
	int i, len;
	char *pstr;
	unsigned char *pdata;

	if(0x8019 == op->id) pdata = (unsigned char *)ParaUniG.termip.username;
	else pdata = (unsigned char *)ParaUniG.termip.pwd;

	if(0 == flag)
	{
		for(len=0; len<32; len++)
		{
			if((pdata[len] == 0) || (pdata[len] == 0xaa))
				break;
		}
	
		pstr = (char *)op->buf;
		/*by ydl modify 2011-05-18*/
		for(i=0; i<len; i++)
		{
			//op->buf[i] = pdata[len-1-i];
			op->buf[i] = pdata[i];
		}
		for(i=len; i<32; i++)
		{
			//op->buf[i] = 0xaa;
			op->buf[i] = 0x00;/*���������λ���������*/
		}
	}
	else
	{
		for(len=0; len<31; len++)
		{
			if((0xaa == op->buf[len]) || (0 == op->buf[len]))
				break;
		}

		/*by ydl modify 2011-05-18*/
		for(i=0; i<len; i++)
		{
			//pdata[i] = op->buf[len-1-i];
			pdata[i] = op->buf[i];
		}
		for(i=len; i<32; i++)
			pdata[i] = 0;
	}

	return 0;
}

/*
Func Description: �ն�ʱ��
Func Param:
	flag: 0-��, 1-д
	op: ��������ָ��
Func Return: ITORTN_*
*/
int paraterm_time(unsigned char flag, itemop_t *op)
{
	sysclock_t clock;
	if(0 == flag)
	{
		SysClockRead(&clock);

		op->buf[0] = clock.second;
		op->buf[1] = clock.minute;
		op->buf[2] = clock.hour;
		op->buf[3] = clock.day;
		op->buf[4] = clock.month;
		op->buf[5] = clock.year;

		hextobcd(op->buf, 6);

		return 0;
	}
	else
	{
		extclock_t extclock;
		utime_t utimecur, utime;
		int i;
		SysClockRead(&clock);
		bcdtohex(op->buf, 6);
		clock.year = op->buf[5];
		clock.month = op->buf[4];
		clock.day = op->buf[3];
		clock.hour = op->buf[2];
		clock.minute = op->buf[1];
		clock.second = op->buf[0];
		//clock.week = time_getweek(PMNTIME_CLK(&clock));
		utimecur = UTimeReadCurrent();
		utime = SysClockToUTime(&clock);
		SysClockSet(&clock);
		SysClockRead(&clock);
		extclock.century = 0;
		extclock.year = clock.year;
		extclock.month = clock.month;
		extclock.day = clock.day;
		extclock.hour = clock.hour;
		extclock.minute = clock.minute;
		extclock.second = clock.second;
		extclock.week = clock.week;
		ExtClockWrite(&extclock);

		if(utimecur > utime) i = utimecur - utime;
		else i = utime - utimecur;

		if(i > 300) SysRecalAllRTimer();
		if(op->mid == 0xffff){
		
		}
		return 0;
	}
}
/*
Func Description: ʵʱУʱ
Func Param:
	flag: 0-��, 1-д
	op: ��������ָ��
Func Return: ITORTN_*
*/
int paraterm_realtime(unsigned char flag, itemop_t *op)
{
	sysclock_t clock;
	if(0 == flag)
	{

		return 1;
	}
	else
	{
		extclock_t extclock;
		utime_t utimecur, utime;
		int i;
		SysClockRead(&clock);
		utimecur = UTimeReadCurrent();
		utime = UTimeReadCurrent();
		if(op->buf[1]&0x80){//��
			op->buf[1]&=0x7f;
			i = make_short(op->buf);
			utime-=i;
		}
		else{//��
			op->buf[1]&=0x7f;
			i = make_short(op->buf);
			utime+=i;
		}
		UTimeToSysClock(utime,&clock);
		SysClockSet(&clock);
		SysClockRead(&clock);
		extclock.century = 0;
		extclock.year = clock.year;
		extclock.month = clock.month;
		extclock.day = clock.day;
		extclock.hour = clock.hour;
		extclock.minute = clock.minute;
		extclock.second = clock.second;
		extclock.week = clock.week;
		ExtClockWrite(&extclock);
		
		if(utimecur > utime) i = utimecur - utime;
		else i = utime - utimecur;

		if(i > 300) SysRecalAllRTimer();
		if(op->mid == 0xffff){
		
		}

		return 0;
	}
}

/*
Func Description: �˿�ֹͣλ
Func Param:
	flag: 0-��, 1-д
	op: ��������ָ��
Func Return: ITORTN_*
*/
int paraterm_port_stopbit(unsigned char flag, itemop_t *op)
{
	int idx;

	idx = (int)((op->id - 0x8700)>>4);
	if(idx) idx--;
	if((idx<0) || (idx>=PORTCFG_NUM)) return ITORTN_INVALID;

	if(0 == flag)
	{
		if(3 == ParaTermG.port[idx].stopbits)op->buf[0] = 1;
		else if(1 == ParaTermG.port[idx].stopbits)op->buf[0]=0;
		else op->buf[0] = 2;
	}
	else
	{
		if(1 == op->buf[0])ParaTermG.port[idx].stopbits=3;
		else if(0 == op->buf[0])ParaTermG.port[idx].stopbits = 1;
		else ParaTermG.port[idx].stopbits = 2;
	}

	return 0;
}
int paraterm_upreaddev(unsigned char flag, itemop_t *op)
{
	unsigned short id;
	unsigned char startdev;
	id = op->id -0x8815;//0Ϊ0x8815,1Ϊ0x8816
	if(0 == flag){
		if(0 == id)startdev = ParaTermG.task_starthour;			
		else startdev = ParaTermG.task_startdev;
		hextobcd(&startdev,1);
		op->buf[0] = startdev;
	}
	else{
		startdev = op->buf[0];
		bcdtohex(&startdev,1);
		if(0 == id)ParaTermG.task_starthour = startdev;
		else ParaTermG.task_startdev= startdev;

	}
	return 0;			
		
}
int paraterm_updaydata(unsigned char flag, itemop_t *op)
{
	unsigned char daytime;

	if (flag  == 0)
	{
		daytime = ParaTermG.hour_updaydata;
		if (daytime != 0xff)
		{
			hextobcd(&daytime, 1);
		}
		op->buf[0] = daytime;
	}
	else
	{
		daytime = op->buf[0];
		if (daytime != 0xff)
		{
			bcdtohex(&daytime, 1);
		}
		
		if (daytime == 0xff ||daytime<=23)
		{
			ParaTermG.hour_updaydata = daytime;

		}
		else
		{
			return 1;
		}
	}

	return 0;
}

int paraterm_scenelist(unsigned char flag, itemop_t *op)
{
	if(flag == 0)
	{
		int  iscene,mask = 1,tempmask;
		unsigned char *pu = op->buf, haveflag=0;
		op->buf[0] = 0x00;
		pu++;
		DebugPrint(0, "1.read paraterm_scenelist\n");
		for(iscene=0;iscene<MAX_SCENECLASS;iscene++)
		{
			if(ParaSceneUse.scenecls[iscene].id == 0) continue;
			
			tempmask = mask<<iscene;
			if(tempmask&ParaSceneUse.flag)
			{
				haveflag = 1;//�������ж��Ƿ����龰
				*pu++ = ParaSceneUse.scenecls[iscene].id;//�龰���(1~16)
				*pu++ = ParaSceneUse.scenecls[iscene].num;
				DebugPrint(0, "2.read paraterm_scenelist:%s\n",ParaSceneUse.scenecls[iscene].scene_name);
				memcpy(pu,ParaSceneUse.scenecls[iscene].scene_name,16);
				pu+=16;
				op->buf[0]++;	//�龰����1
			}
		}
		DebugPrint(0, "read paraterm_scenelist haveflag = %d\n",haveflag);
		if(!haveflag && iscene>=MAX_SCENECLASS) 
		{
			op->actlen = 0;
			return -1;//�龰�б�Ϊ��
		}
		op->actlen = (pu-op->buf)&0xffff;

		DebugPrint(0, "read paraterm_scenelist op->actlen = %d\n",op->actlen);
	}
	return 0;
}
int paraterm_cameralist(unsigned char flag, itemop_t *op)
{
	if(0 == flag)
	{
		int   icamera;
		unsigned char *pu = op->buf;
		memset(pu,0x00,340);
		for(icamera = 0;icamera<MAX_CAMERA_NUM;icamera++)
		{
			if(ParaTermG.camerainfo[icamera].index>0)
			{
				pu[icamera*85+0] = ParaTermG.camerainfo[icamera].index;
				pu[icamera*85+1] = ParaTermG.camerainfo[icamera].nchanel;
				pu[icamera*85+2] = ParaTermG.camerainfo[icamera].fac_type;
				pu[icamera*85+3] = ParaTermG.camerainfo[icamera].net_port&0xff;
				pu[icamera*85+4] = (ParaTermG.camerainfo[icamera].net_port>>8)&0xff;				
				memcpy(&pu[icamera*85+5],ParaTermG.camerainfo[icamera].net_addr,32);
				memcpy(&pu[icamera*85+37],ParaTermG.camerainfo[icamera].username,16);
				memcpy(&pu[icamera*85+53],ParaTermG.camerainfo[icamera].password,16);
				memcpy(&pu[icamera*85+69],ParaTermG.camerainfo[icamera].videoname,16);
			}
			else
				continue;
		}
	}
	return 0;
}
int paraterm_timertasklist(unsigned char flag, itemop_t *op)
{
	if(0 == flag)
	{
		int   index;
		unsigned char *pu = op->buf;
		memset(pu,0x00,340);
		for(index = 0;index<MAX_TIMERTASK;index++)
		{
			//if(ParaTimerTask[index].id>0)
			{
				smallcpy(&pu[index*22+0], &ParaTimerTask[index].id,22);
				/*pu[index*22+0] = ParaTimerTask[index].id;
				pu[index*22+1] = ParaTimerTask[index].num;
				memcpy(&pu[index*22+2],ParaTimerTask[index].task_name,16);
				pu[index*22+18] = ParaTimerTask[index].hour;
				pu[index*22+19] = ParaTimerTask[index].min;
				pu[index*22+20] = ParaTimerTask[index].weekflag;
				pu[index*22+21] = ParaTimerTask[index].bStart;*/
			}

		}
	}
	return 0;
}

int paraterm_scene(unsigned char flag, itemop_t *op)
{
	unsigned char i;
	unsigned char *pu = &op->buf[0];
	unsigned short id = (op->id&0x0f)+1;//�龰���,��1��ʼ
	DebugPrint(0,"id = %d\n",id);
	if(id<1 || id>MAX_SCENECLASS ) return -1;
	if(0 == flag){//��ȡ	
		for(i=0; i<MAX_SCENECLASS; i++){
			if(id == ParaSceneUse.scenecls[i].id) break;
		}
		DebugPrint(0,"i = %d,sizeof(cfg_scenecls_data_t)=%d\n",i,sizeof(cfg_scenecls_data_t));
		if(i >= MAX_SCENECLASS) return -1;
		smallcpy((char *)pu, &ParaSceneUse.scenecls[i], sizeof(cfg_scenecls_data_t));
		pu+= sizeof(cfg_scenecls_data_t);
		//�龰ID
		/**pu++ = id&0xff;	
		*pu++ = ParaSceneUse.scenecls[i].num;
		smallcpy((char *)pu, ParaSceneUse.scenecls[i].scene_name, 16);
		pu += 16;
		devnum = ParaSceneUse.scenecls[i].num;
		for(j=0; j<devnum; j++){
		//	if(ParaSceneUse.scenecls[i].met[j].metid == 0 || ParaSceneUse.scenecls[i].met[j].metid == 0xffff) continue;
			*pu++=ParaSceneUse.scenecls[i].met[j].attr;
			depart_short(ParaSceneUse.scenecls[i].met[j].metid, pu);
			pu += 2;
			smallcpy(pu, ParaSceneUse.scenecls[i].met[j].state, 8);
			pu += 8;
		}*/
		//op->actlen = (pu-op->buf)&0xffff;
	}else{//����
		////���������ǰ��Ҫ���õ��龰,������д��
		unsigned char  sceneid = op->buf[0];
		if(sceneid>MAX_SCENECLASS)	//�������龰
		{
			for(i=0; i<MAX_SCENECLASS; i++)
			   if(0x00 == ParaSceneUse.scenecls[i].id) break;
			   
			if(i>=MAX_SCENECLASS)
				return -1;	//���ʧ��
			
			smallcpy(&ParaSceneUse.scenecls[i],(char *)pu,sizeof(cfg_scenecls_data_t));
			ParaSceneUse.scenecls[id-1].id = i;			
			
		}
		else if(sceneid == 0) //ɾ���龰
		{
		
			memset(&ParaSceneUse.scenecls[id-1].id, 0, sizeof(cfg_scenecls_data_t));
		}
		else					//�޸��龰
		{
			DebugPrint(0,"i = %d,�޸��龰sizeof(cfg_scenecls_data_t)=%d\n",i,sizeof(cfg_scenecls_data_t));
			smallcpy(&ParaSceneUse.scenecls[id],(char *)pu,sizeof(cfg_scenecls_data_t));
		}
		
	}
	return 0;
}

int paraterm_timertask(unsigned char flag, itemop_t *op)
{
	unsigned char *pu = op->buf, i;
	unsigned short id = (op->id&0x0f);//�龰���,��1��ʼ
	
	if(id<1 || id>MAX_SCENECLASS ) return -1;
	if(0 == flag){//��ȡ	
		for(i=0; i<MAX_TIMERTASK; i++){
			if(id == ParaTimerTask[i].id) break;
		}
		if(i >= MAX_TIMERTASK) return -1;
		memcpy(pu,&ParaTimerTask[i],sizeof(cfg_timertaskcls_data_t));
	}else{//����
		for(i=0; i<MAX_TIMERTASK; i++){
			if(id == ParaTimerTask[i].id) break;
		}
		if(*pu >MAX_TIMERTASK)	//����������
		{
			for(i=0; i<MAX_TIMERTASK; i++)		//���ҿ���ӵ�λ��
				if(0 == ParaTimerTask[i].id) break;
			if(i>=MAX_TIMERTASK)		//�龰���Ѵ������
				return -1;

			smallcpy(&ParaTimerTask[i],pu,sizeof(cfg_timertaskcls_data_t));
			ParaTimerTask[i].id = i;	//��������ID
			return 0;
		}
		else if( 0 == *pu )	//ɾ������
		{
			memset(&ParaTimerTask[id-1].id, 0, sizeof(cfg_timertaskcls_data_t));
		}
		else
		{
			smallcpy(&ParaTimerTask[i],pu,sizeof(cfg_timertaskcls_data_t));
		}		
	}
	return 0;
}


int paraterm_daylinewase(unsigned char flag, itemop_t *op)
{

	 return 0;
}

int paraterm_monlastread(unsigned char flag, itemop_t *op)
{
	unsigned char tmpbuf[2];

	if (flag == 0)
	{
		tmpbuf[0] = ParaTermG.hour_read_mondata;
		tmpbuf[1] = ParaTermG.day_read_mondata;
		hextobcd(tmpbuf, 2);

		op->buf[0] = tmpbuf[0];
		op->buf[1] = tmpbuf[1];
	}
	else
	{
		tmpbuf[0] = op->buf[0];
		tmpbuf[1] = op->buf[1];
		bcdtohex(tmpbuf, 2);

		if (tmpbuf[0] <=23 && tmpbuf[1] <= 28)
		{
			ParaTermG.day_read_mondata = tmpbuf[1];
			ParaTermG.hour_read_mondata = tmpbuf[0];
		}
		else
		{
			return 1;
		}
	}

	return 0;
}

int paraterm_monlastup(unsigned char flag, itemop_t *op)
{
	unsigned char tmpbuf[2];

	if (flag == 0)
	{
		tmpbuf[0] = ParaTermG.hour_up_mondata;
		tmpbuf[1] = ParaTermG.day_up_mondata;
		if (tmpbuf[0] != 0xff && tmpbuf[1]!= 0xff)
		{
			hextobcd(tmpbuf, 2);
		}
		
		op->buf[0] = tmpbuf[0];
		op->buf[1] = tmpbuf[1];
	}
	else
	{
		tmpbuf[0] = op->buf[0];
		tmpbuf[1] = op->buf[1];
		if (tmpbuf[0] != 0xff && tmpbuf[1]!= 0xff)
		{
			bcdtohex(tmpbuf, 2);
		}
		if ( (tmpbuf[0] <=23||tmpbuf[0]==0xff) && (tmpbuf[1] <= 28||tmpbuf[1]==0xff) )
		{
			ParaTermG.day_up_mondata = tmpbuf[1];
			ParaTermG.hour_up_mondata = tmpbuf[0];
		}
		else
		{
			return 1;
		}
	}

	return 0;
}

/*
func:����ַ��ȡ������
*/
int paraterm_peibian_addr(unsigned char flag, itemop_t *op)
{
	int tmp;
	
	int datalen;
	datalen = sizeof(ParaTermG.peibian_addr);
	DebugPrint(0, "datalen:%d\n", datalen);

	if (flag == 0)
	{
		memcpy(op->buf, ParaTermG.peibian_addr, 4);
		tmp = op->buf[2];
		op->buf[2] = op->buf[3];
		op->buf[3] = tmp;
		BuffRev((char *)op->buf, 4);
	}
	else
	{
		BuffRev((char *)op->buf, 4);
		tmp = op->buf[2];
		op->buf[2] = op->buf[3];
		op->buf[3] = tmp;
		memcpy(ParaTermG.peibian_addr, op->buf, 4);
	}

	return 0;
}

/*
func:�ն˸�λ
*/
int paraterm_reset(unsigned char flag, itemop_t *op)
{
	
	int datalen;
	int timer = 0;
	datalen = 2;
	DebugPrint(0, "datalen:%d\n", datalen);
	unsigned char resetcmd;
	if (flag == 1)
	{	
		resetcmd = op->buf[0];
		DebugPrint(0, "resetcmd:%d\n", resetcmd);
		switch(resetcmd)
		{
			case 0x01:	//�豸Ӳ����λλ
				
				timer =SysAddCTimer(5, CTimerSysRestart, 0);
				DebugPrint(0,"�豸Ӳ����λtimer=%d\n",timer);
				SysRestart();
			case 0x05:	//�������
				break;
			case 0x06:	//����
				ParaTermG.alarm_flag|=0x08; 
				BeepSound(2);
				SaveParaTerm();
				break;
			case 0x07: 	//����
				ParaTermG.alarm_flag&=~0x08; 
				BeepSound(1);
				SaveParaTerm();
				break;
		}
	}

	return 0;
}
/*
func:ֹͣ������ָ���豸�������ݲ���
*/
int paraterm_sampling(unsigned char flag, itemop_t *op)
{
	unsigned char cmd = op->buf[0];
	unsigned char timespan = op->buf[1];	//����ʱ����
	unsigned short metid = op->buf[2];
	if(timespan<3)
		timespan = 3;
	if (flag == 1)
	{	
		switch(cmd)
		{
			case 0x00:	//ֹͣ����
				if(TimeSamplingId < 0) TimeSamplingId = SysAddCTimer(timespan, CTimerSamplingData, metid);
				else 
				{
					SysClearCTimer(TimeSamplingId);
					TimeSamplingId = SysAddCTimer(timespan, CTimerSamplingData, metid);
					
				}
				break;
			case 0x01:	//��ʼ����
				if(TimeSamplingId >= 0) SysClearCTimer(TimeSamplingId);
				break;
		}
	}
	PlcSamplingMetid = metid;
	return 0;
}




