/**
* diskspace.c -- �����������ʣ��ռ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-6-16
* ����޸�ʱ��: 2009-6-16
*/

#include <stdio.h>
#include <sys/vfs.h>
#include <string.h>
#include <stdlib.h>

/**
* @brief ��������Ŀռ�������
* @param diskpath ������
* @return �ɹ����ؿռ�������(1%), ʧ�ܷ���-1
*/
int DiskUsage(const char *diskpath)
{
	struct statfs buffer;
	int rtn;

	if(statfs(diskpath, &buffer)) return -1;

	if(buffer.f_blocks <= 0) return -1;


	rtn = (buffer.f_blocks - buffer.f_bavail)*100/buffer.f_blocks;
	//rtn = (int)((float)buffer.f_bavail/(float)buffer.f_blocks)*100;
	return rtn;
}

void setvolume(int volume)
{
	char  musicvolume[100] ={0};
	sprintf(musicvolume,"numid=5,iface=MIXER,name='Headphone Playback Volume' %d",volume);
	system(musicvolume);
}

