/**
* file.h -- �ļ������ӿ�ͷ�ļ�
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-3-31
* ����޸�ʱ��: 2009-3-31
*/

#ifndef _SYS_FILE_H
#define _SYS_FILE_H

#include <stdio.h>

int SysGetFileSize(FILE *pf);
void SysRemoveOneFile(const char *file);
int SysRemoveFiles(const char *files);

#endif /*_SYS_FILE_H*/
