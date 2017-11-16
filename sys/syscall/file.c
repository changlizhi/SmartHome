/**
* file.c -- �ļ������ӿ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2008-5-16
* ����޸�ʱ��: 2009-3-30
*/


#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <linux/reboot.h>
#include <sys/reboot.h>
#include <dirent.h>
#include "include/debug.h"
/**
* @brief ����ļ���С(���ֽ�Ϊ��λ)
* @param pf �ļ�ָ��
*/
int SysGetFileSize(FILE *pf)
{
	long start, end;

	fseek(pf, 0, SEEK_END);
	end = ftell(pf);
	fseek(pf, 0, SEEK_SET);
	start = ftell(pf);

	return(end-start);
}

///����������
#define MAXLEN_PATH		64
#define MAXLEN_HEAD		16
#define MAXLEN_TAIL		16

/**
* @brief �����ļ���������
* @param src ������
* @param path ���������·����
* @param filterhead ���������ͨ���ǰ�ļ���
* @param filtertail ���������ͨ������ļ���
* @return 0��ʾ�ɹ�, ����ʧ��
*/
static int parseFilter(const char *src, char *path, char *filterhead, char *filtertail)
{
	int i = strlen(src);
	int pos;

	if(i >= MAXLEN_PATH) return 1;

	for(pos=i-1; pos >=0; pos--) {
		if('/' == src[pos]) break;
	}

	if(pos <= 0) {
		strcpy(path, "./");
	}
	else {
		for(i=0; i<=pos; i++) *path++ = *src++;
		*path = 0;
	}

	i = 0;
	pos = 0;
	for(; 0!=*src; src++) {
		if('*' == *src) {
			pos = 0;
			i = 1;
		}
		else if(0 == i) {
			*filterhead++ = *src;
			pos++;
			if(pos >= MAXLEN_HEAD) return 1;
		}
		else {
			*filtertail++ = *src;
			pos++;
			if(pos >= MAXLEN_TAIL) return 1;
		}
	}
	*filterhead = 0;
	*filtertail = 0;

	return 0;
}

/**
* @brief �Ƚ��ļ����������
* @param file �ļ���
* @param filterhead ���������ͨ���ǰ�ļ���
* @param filtertail ���������ͨ������ļ���
* @return 1��ʾƥ��,0��ʾ��ƥ��
*/
static int compareFilter(const char *file, const char *filterhead, const char *filtertail)
{
	int i, j;

	if(0 != *filterhead) {
		for(i=0; 0!=*filterhead; filterhead++,i++) {
			if(file[i] != *filterhead) break;
			else if(0 == file[i]) break;
		}
		if(0 != *filterhead) return 0;
	}

	if(0 != *filtertail) {
		i = strlen(filtertail);
		filtertail += (i-1);
		j = strlen(file);
		if(i > j) return 0;
		file += (j-1);

		for(j=0; j<i; i--,filtertail--,file--) {
			if(*filtertail != *file) break;
		}
		if(j >= i) return 1;
		else return 0;
	}

	return 1;
}

/**
* @brief ɾ��һ���ļ�
* @param file �ļ���
*/
void SysRemoveOneFile(const char *file)
{
	remove(file);
}

/**
* @brief ɾ������ļ�
* @param files �ļ���������, ��"*.dat", "k*", "y*.c"�ȵ�
* @return 0��ʾ�ɹ�,�����ʾʧ��
* @note ��ò�Ҫ�������������ļ������߹���·����(�ܺͲ��ܳ���64�ֽ�),
      �������Ч�ʲ���󽵵�
*/
int SysRemoveFiles(const char *files)
{
	DIR *dir;
	struct dirent *ptr;
	char path[MAXLEN_PATH], filterhead[MAXLEN_HEAD], filtertail[MAXLEN_TAIL];
	char *filename;
	int pathlen;

	if(parseFilter(files, path, filterhead, filtertail)) return 1;
	//print_logo(0, "rm files %s*%s in %s\n", filterhead, filtertail, path);
	filename = path;
	pathlen = strlen(path);
	filename += pathlen;

	dir = opendir(path);
	if(NULL == dir) {
		PrintLog(0,"open dir failed\n");
		return 1;
	}

	while((ptr = readdir(dir)) != NULL) {
		//printf("dir: %d: %s\n", ptr->d_type, ptr->d_name);
		if(DT_REG != ptr->d_type) continue;

		if(compareFilter(ptr->d_name, filterhead, filtertail)) {
			if((pathlen+strlen(ptr->d_name)) >= MAXLEN_PATH) {  //too long
				char *tmppath, *tmpptr;
				int i;

				tmppath = malloc(pathlen+strlen(ptr->d_name)+1);
				if(NULL != tmppath) {
					tmpptr = tmppath;
					for(i=0; i<pathlen; i++) *tmpptr++ = path[i];
					for(i=0; i<strlen(ptr->d_name); i++) *tmpptr++ = ptr->d_name[i];
					*tmpptr = 0;
					remove(tmppath);
					free(tmppath);
				}
			}
			else {
				strcpy(filename, ptr->d_name);
				//print_logo(0, "remove %s...\n", path);
				remove(path);
			}
		}
	}

	closedir(dir);
	return 0;
}

