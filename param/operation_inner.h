/**
* operation_inner.h -- ��������ͷ�ļ�(�ڲ�ʹ��)
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-7
* ����޸�ʱ��: 2009-5-7
*/

#ifndef _PARAM_OPERATION_INNER_H
#define _PARAM_OPERATION_INNER_H

int SaveParaTerm(void);
int LoadParaTerm(void);
int LoadParaUni(void);
int LoadParaDataUse(void);
int LoadParaTimerTask(void);


void SetSaveParamFlag(unsigned int flag);
void SaveParam(void);


#endif /*_PARAM_OPERATION_INNER_H*/

