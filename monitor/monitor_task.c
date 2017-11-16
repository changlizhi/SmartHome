/**
* monitor_task.c -- ���ģ������
* 
* ����: yangzhilong
* ����ʱ��: 2009-10-30
* ����޸�ʱ��: 2009-10-30
*/

#include <sys/types.h>  
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>  
#include <unistd.h> 
#include <fcntl.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <sys/errno.h>
#include <poll.h>
#include <sys/stat.h>

#include "include/basetype.h"
#include "include/debug/shellcmd.h"
#include "include/debug.h"
#include "include/param/term.h"
#include "include/sys/schedule.h"
#include "include/sys/gpio.h"
#include "include/sys/reset.h"
#include "include/sys/timeal.h"
#include "include/sys/timer.h"
#include "include/sys/task.h"
#include "include/sys/cycsave.h"
#include "include/sys/syslock.h"
#include "include/lib/bcd.h"
#include "downlink/plmdb.h"
#include "include/uplink/svrnote.h"
#include "../uplink/svrcomm.h"


#include "include/monitor/alarm.h"
#include "downlink/plcomm.h"
//static int TimerIdPowerOff = -1;
#define USB_DISK   "/dev/sda1"
#define TMP_UDISK    TEMP_PATH"udisk.tmp" //��ʱ�ļ�
#define UDISKPARAM     "fdisk -l /dev/sd?" //���U�̹����̷�

#define TMP_SERIAL    TEMP_PATH"serial.tmp" //��ʱ�ļ�

unsigned char termtousb=0;//0:������U�̸��³����ն�,1���ն˿������ݵ�U��
unsigned char udiskname[96];//�̷���
static int USBLockId = -1;//��Դ��
static int USBUartLockId = -1;//��Դ��
int udisk = -1;//�ļ���//�̷����ļ�ID

extern unsigned char hard_info[18];
extern unsigned char	 audiourl[512];

extern unsigned char  	 UpdateAudiourlFlag;

unsigned char wifi_down_musice_state=0;
unsigned char wifi_update_system_state=0;
/**
* @brief У׼ϵͳʱ��
*/

extern void MakeAlarmG(alarm_buf_t *pbuf);
extern void SaveAlarm(alarm_buf_t *pbuf);
extern void UpdateAlarm(alarm_buf_t *pbuf);
extern alarm_buf_t * GetCurrentAlarm();
static int currentButtonState = -1; //0--Ϊֹͣ״̬��1--Ϊ����״̬

static void SysClockCilibrate(void)
{
	sysclock_t clock;

	if(ReadExternSysClock(&clock)) return;

	SysClockSet(&clock);
}

#define CYCSAVE_TIMEOUT		(7*3500)    // 7 hour
#define CYCSAVE_FIRSTCNT		(3*3500)    // 3 hour
#define DBCLR_TIMEOUT			(16*3500)  // 16 hour
#define DBCLR_FIRSETCNT		(2*3500)   // 2 hour
#define CLKCHK_TIMEOUT			(5*3500)   // 5 hour

//������Ƶ�ļ� 
//filename �ļ�����
//type �ļ�����1--��Ƶ�����ļ���0--������ʾ�ļ�
static int PlayVoice(const char * filename,int type)
{
	char cmd[128]={0};
	char dir[80] = {0};
	system("killall -9 madplay");
	system("killall -9 aplay");
	int filestat = 0;
	if(type == 1)
	{
		filestat = getFileDays();//�ж���Ƶ�ļ��Ƿ���Ч
		PrintLog(0,"getFileDays %d",filestat);
		if(filestat !=0)
		{
			//��Ƶ�ļ�ʧЧ��������ʾ��
			sprintf(cmd,"aplay /tmp/mounts/SD-P1/voice/musicefileInvalid.wav  &");
			system(cmd);
			Sleep(1);
			//�л���Ƶ���ſ���
			gpio_set_value(GPIO_39,1);
			gpio_set_value(GPIO_42,1);
			return -1;
		}
		else if(access("/tmp/mounts/SD-P1/play/shock.mp3",F_OK)==0)
		{
			//��Ƶ��Ч����ѭ��������Ƶ�ļ�
			sprintf(cmd,"madplay /tmp/mounts/SD-P1/play/%s -r &",filename);
			system(cmd);
			Sleep(1);
			//�л���Ƶ���ſ���
			gpio_set_value(GPIO_39,0);
			gpio_set_value(GPIO_42,0);
			return 0;
		}
		else
		{
			//����Ƶ�ļ���������ʾ��
			sprintf(cmd,"aplay /tmp/mounts/SD-P1/voice/musicefileInvalid.wav  &");
			system(cmd);
			Sleep(1);
			gpio_set_value(GPIO_39,1);
			gpio_set_value(GPIO_42,1);
			return -1;
		}
		
		
		
	}
	else if(type == 0)
	{
		//����ָ���ļ�������ʾ��
		sprintf(cmd,"aplay /tmp/mounts/SD-P1/voice/%s  &",filename);
		
		system(cmd);
		Sleep(1);
		gpio_set_value(GPIO_39,1);
		gpio_set_value(GPIO_42,1);
		return 0;

	}
}

/**
* @brief �������
*/
extern void DbaseClear(void);
//������Ƶ���ż�¼��ͳ�Ʋ���ʱ���������ļ��У����豸��¼�������ϴ���������
static void *UpdateAlarmTask_Monitor(void *arg)
{
	static int times = 0;
	while(1){
		
		if(currentButtonState == 1)
		{
			times++;
			if(times >= 30)
			{
				PrintLog(0,"UpdateAlarmTask_Monitor");
				UpdateAlarm(GetCurrentAlarm());
				times = 0;
			}
		}
		else if(currentButtonState == 0 ||currentButtonState == -1)
		{
			times = 0;
		}
		Sleep(100);

		
		if(exitflag)
			break;
	}
	return 0;
}


static void *NetLedTask_Monitor(void *arg)
{
	static int lednet = 1;
	int  times = 0;
	while(1){
		if(UpdateAudiourlFlag == 1)
		{
			gpio_set_value(GPIO_LED_NET,1);
			Sleep(10);
			gpio_set_value(GPIO_LED_NET,0);
			Sleep(10);
		}
		else if(SvrCommLineState == LINESTAT_ON)
		{
			gpio_set_value(GPIO_LED_NET,0);
			Sleep(100);
		}
		else if(SvrCommLineState == LINESTAT_OFF)
		{
			times++;
			if(times>1000);
			{
			 	gpio_set_value(GPIO_LED_NET,lednet);
				times = 0;
				if(lednet == 0)
					lednet = 1;
				else
					lednet = 0;
			}

		}
		Sleep(1000);
		if(exitflag)
			break;
	}
	return 0;
}

//���������ļ�������
static void *SysLedTask_Monitor(void *arg)
{
	while(1){
		gpio_set_value(GPIO_LED_SYS,1);
			Sleep(100);
		gpio_set_value(GPIO_LED_SYS,0);
		Sleep(100);
		if(exitflag)
			break;
	}
	return 0;
}

//���������ļ�������
static void *DownLoadMusicTask_Monitor(void *arg)
{
	char downloadcmd[512] = {0};
	struct	stat 	buf;
	int 	reseult;
	int 	filestat = 0;
	int 	firstDownTaskCheck = 1;
	while(1){
		if(UpdateAudiourlFlag ||(1 == firstDownTaskCheck)||(1==ParaTermG.login_update_system)) //��������״̬
		{
			reseult = stat("/tmp/mounts/SD-P1/music.zip",&buf);

			PrintLog(0,"music.zip size:%d,create time:%s",buf.st_size,ctime(&buf.st_ctime));
			PrintLog(0," in downloadMusic Task stop play...\n");
			

			 if(1 == firstDownTaskCheck)
			 {
			 	wifi_down_musice_state = 1;
				PrintLog(0," in firstDownTaskCheck Task stop play...\n");
				system("wifi up");
			 	memset(downloadcmd,0,512);
				sprintf(downloadcmd,"sh /opt/work/musicdownload.sh");
				system(downloadcmd);
				firstDownTaskCheck = 0;
				wifi_down_musice_state = 0;
			 }
			 if(1==ParaTermG.login_update_system)
			 {
			 	wifi_down_musice_state = 1;
				PrintLog(0," in firstDownTaskCheck Task stop play...\n");
				system("wifi up");
			 	memset(downloadcmd,0,512);
				sprintf(downloadcmd,"sh /opt/work/musicdownload.sh");
				system(downloadcmd);
				ParaTermG.login_update_system = 0;
				wifi_down_musice_state = 0;
			 }
			 else
			 {
				wifi_down_musice_state = 1;
				system("wifi up");
				PlayVoice("startdownload.wav",0);
				currentButtonState = 0;
						
				memset(downloadcmd,0,512);
				sprintf(downloadcmd,"sh /opt/work/musicdownload.sh %s",audiourl);
				system(downloadcmd);
				PlayVoice("enddownload.wav",0);
				system("wifi down");
				PrintLog(0,"downloadMusic Task Finshed...\n");
				
				wifi_down_musice_state = 0;
				
				UpdateAudiourlFlag = 0;
			}
			
			
			
		}
		Sleep(10);
		if(exitflag)
			break;
	}
	return 0;
}
//ϵͳԶ�������������
static void *UpdateSystemTask_Monitor(void *arg)
{
	char systemcheckcmd[512] = {0};
	int  checktime = 600;
		while(1){
			 if(checktime>600)
			 {
				wifi_update_system_state = 1;
			 	PrintLog(0," in UpdateSystemTask_Monitor Task stop play...\n");
				memset(systemcheckcmd,0,512);
				sprintf(systemcheckcmd,"sh /opt/work/ftup.sh");
				system(systemcheckcmd);
				wifi_update_system_state = 0;
				checktime=0;
			 }
		 	if(1==ParaTermG.login_update_system)
			 {
				wifi_update_system_state = 1;
			 	PrintLog(0," in UpdateSystemTask_Monitor Task stop play...\n");
				memset(systemcheckcmd,0,512);
				sprintf(systemcheckcmd,"sh /opt/work/ftup.sh");
				system(systemcheckcmd);
				ParaTermG.login_update_system = 0;
				wifi_update_system_state = 0;
				checktime=0;
			 }
			Sleep(1000);
			checktime++;
			if(exitflag)
				break;
		}
		return 0;

}


//��ⲥ�Ű��������¼�
static void *PlayTask_Pressdown(void *arg)
{
	
	static int presstimes = 0;
	unsigned int value = 0;
	int  playstate = 0;
	gpio_export(GPIO_PLAY);
	gpio_set_dir(GPIO_PLAY, 0);
	gpio_set_edge(GPIO_PLAY, "rising");

	currentButtonState  = 0;
	PrintLog(0,"ParaTermG.first_start %d...\n",ParaTermG.first_start);
	
	if(ParaTermG.first_start)
	{
		PlayVoice("welcome.wav",0);
		
	}
	else
	{
		PlayVoice("welcome1.wav",0);
	}
	system("sh /opt/work/unzipmusic.sh");
	
	while (1) {

			gpio_get_value(GPIO_PLAY,&value);
			if(value == 0 )
			{
				presstimes++;
				
				
			}
			else if(value == 1)
			{
				if(presstimes>5)
				{
					
					if(currentButtonState == 0)
					{
						if(UpdateAudiourlFlag == 0)
						{
							
							PlayVoice("startplay.wav",0);
							
							Sleep(300);
							
							playstate = PlayVoice("shock.mp3",1);
							if(playstate == 0)
							{
								MakeAlarmG(GetCurrentAlarm());
								currentButtonState = 1;
								PrintLog(0,"play button press to start play...\n");
								//system("wifi down");
								SvrCommLineState = LINESTAT_OFF;
							}
							
						}
						else if(UpdateAudiourlFlag == 1)
						{
							PlayVoice("downloading.wav",0);
						}
						
					}
					else if(currentButtonState == 1)
					{
						if(UpdateAudiourlFlag == 1)
						{
							PlayVoice("downloading.wav",0);
						} 
						else if(UpdateAudiourlFlag == 0)
						{
							PrintLog(0,"play button press to stop play...\n");
							system("killall -9 madplay");
							PrintLog(0,"play button press to stop play1...\n");

							SaveAlarm(GetCurrentAlarm());
							gpio_set_value(GPIO_42,1);
							gpio_set_value(GPIO_39,0);
							//system("wifi up");
							PrintLog(0,"play button press to stop play2...\n");

							PlayVoice("stopplay.wav",0);
							PrintLog(0,"play button press to stop play3...\n");

							currentButtonState = 0;
						}
					}
					presstimes = 0;
				}
			}
		Sleep(1);
	if(exitflag)
	{

		break;
	}
	}
	return 0;
}
//����������������¼�
static void *VolumeBtn_Pressdown(void *arg)
{
	

	static int pressaddtimes = 0;
	static int presssubtimes = 0;
	static int currentVolume = 9;
	unsigned char VolumeLevel[10]={0};
	VolumeLevel[0] = 0;
	VolumeLevel[1] = 40;
	VolumeLevel[2] = 70;
	VolumeLevel[3] = 80;
	VolumeLevel[4] = 90;
	VolumeLevel[5] = 100;
	VolumeLevel[6] = 110;
	VolumeLevel[7] = 120;
	VolumeLevel[8] = 124;
	VolumeLevel[9] = 127;
	char   cmd[100];
	int gpio_fdadd;
	int gpio_fdsub;

	unsigned int value = 0;

	gpio_export(GPIO_KEY_ADD);
	gpio_set_dir(GPIO_KEY_ADD, 0);
	gpio_set_edge(GPIO_KEY_ADD, "rising");
	gpio_fdadd = gpio_fd_open(GPIO_KEY_ADD);
	
	gpio_export(GPIO_KEY_SUB);
	gpio_set_dir(GPIO_KEY_SUB, 0);
	gpio_set_edge(GPIO_KEY_SUB, "rising");
	gpio_fdsub = gpio_fd_open(GPIO_KEY_SUB);

	PrintLog(0,"play current volume is %d...\n",VolumeLevel[currentVolume]);
	
	while (1) {

			gpio_get_value(GPIO_KEY_ADD,&value);
			if(value == 0 )
			{
				pressaddtimes++;
				if(pressaddtimes >400 && presssubtimes<100)
				{
					//if(currentButtonState == 0)
					{
						PlayVoice("enablewifi.wav",0);
						sprintf(cmd,"wifi up");
						system(cmd);
						pressaddtimes = 0;
					}
				}
								
			}
			else if(value == 1)
			{
				if(presssubtimes>800 && pressaddtimes >800)
				{
					PrintLog(0,"1 presssubtimes is %d...pressaddtimes is %d\n",presssubtimes,pressaddtimes);
					sprintf(cmd,"uci set wireless.ap.encryption=\'none\'");
					system(cmd);
					sprintf(cmd,"uci delete wireless.ap.key");
					system(cmd);
					sprintf(cmd,"uci commit");
					system(cmd);
					sprintf(cmd,"uci -c/opt/ft set ftconfig.@ftconfig[0].firststart=1");
					system(cmd);
					sprintf(cmd,"uci -c/opt/ft commit");
					sprintf(cmd,"wifi down");
					system(cmd);
					sprintf(cmd,"wifi up");
					system(cmd);
					PlayVoice("resetwifi.wav",0);
					presssubtimes = 0;
					pressaddtimes = 0;
				}
				if(pressaddtimes>5)
				{
					if(currentVolume<9)
						currentVolume++;
					
					PrintLog(0,"play current volume is %d...\n",VolumeLevel[currentVolume]);
					memset(cmd,0,100);
					sprintf(cmd,"amixer cset numid=9,iface=MIXER,name=\'Headphone Playback Volume\' %d",VolumeLevel[currentVolume]);
					system(cmd);
					pressaddtimes = 0;
				}
			}
			
			gpio_get_value(GPIO_KEY_SUB,&value);
			if(value == 0 )
			{
				presssubtimes++;
				if(presssubtimes >400 &pressaddtimes <100)
				{
					//if(currentButtonState == 0)
					{
						
					PlayVoice("disablewifi.wav",0);
					sprintf(cmd,"wifi down");
						system(cmd);
						presssubtimes = 0;
					}
				}

								
			}
			else if(value == 1)
			{
				if(presssubtimes>800 && pressaddtimes >800)
				{
					PrintLog(0,"1 presssubtimes is %d...pressaddtimes is %d\n",presssubtimes,pressaddtimes);
					sprintf(cmd,"uci set wireless.ap.encryption=\'none\'");
					system(cmd);
					sprintf(cmd,"uci delete wireless.ap.key");
					system(cmd);
					sprintf(cmd,"uci commit");
					system(cmd);
					sprintf(cmd,"uci -c/opt/ft set ftconfig.@ftconfig[0].firststart=1");
					system(cmd);
					sprintf(cmd,"uci -c/opt/ft commit");
					
					sprintf(cmd,"wifi down");
					system(cmd);
					sprintf(cmd,"wifi up");
					system(cmd);
					PlayVoice("resetwifi.wav",0);
					presssubtimes = 0;
					pressaddtimes = 0;
				}
				if(presssubtimes>5)
				{
				
					if(currentVolume>0)
						currentVolume--;
					PrintLog(0,"play current volume is %d...\n",VolumeLevel[currentVolume]);
					memset(cmd,0,100);
					sprintf(cmd,"amixer cset numid=9,iface=MIXER,name=\'Headphone Playback Volume\' %d",VolumeLevel[currentVolume]);
					system(cmd);
					presssubtimes = 0;
				}
			}
			
		Sleep(1);
	if(exitflag)
	{
	  gpio_fd_close(gpio_fdadd);
	  gpio_fd_close(gpio_fdsub);
		break;
	}
	}
	gpio_fd_close(gpio_fdadd);
	gpio_fd_close(gpio_fdsub);
	return 0;
}


DECLARE_INIT_FUNC(MonitorTaskInit);
int MonitorTaskInit(void)
{

	RunStateInit();	
	SysCreateTask(PlayTask_Pressdown, NULL);
	AlarmInit();
	SysCreateTask(UpdateSystemTask_Monitor, NULL);
	SysCreateTask(UpdateAlarmTask_Monitor, NULL);
	SysCreateTask(DownLoadMusicTask_Monitor, NULL);	
	SysCreateTask(NetLedTask_Monitor, NULL);
	SysCreateTask(SysLedTask_Monitor, NULL);		
	SysCreateTask(VolumeBtn_Pressdown, NULL);
	SET_INIT_FLAG(MonitorTaskInit);
	return 0;
}


