/**
* route.h -- ·�ɱ����
* 
* ����: zhuzhiqiang
* ����ʱ��: 2009-5-20
* ����޸�ʱ��: 2009-5-20
*/

#ifndef _PARAM_ROUTE_H
#define _PARAM_ROUTE_H

#include "include/param/capconf.h"
//#include "include/param/term.h"

#define MAX_ROUTE_LEVEL		4  //���·�ɼ���
#define MAX_ROUTE_ONEMET		4  //һ���������·����

typedef struct {
	unsigned char level;  //����
	unsigned char unuse;
	unsigned char addr[MAX_ROUTE_LEVEL*6];
} cfg_route_t;

typedef struct {
	unsigned char num;
	unsigned char unuse[3];
	cfg_route_t route[MAX_ROUTE_ONEMET];
} cfg_route_met_t;

#ifndef DEFINE_PARAROUTE
extern  cfg_route_met_t ParaRoute[MAX_METER];
#endif

#endif /*_PARAM_ROUTE_H*/

