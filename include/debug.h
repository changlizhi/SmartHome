/**
* debug.h -- ������Ϣ����ͷ�ļ�
* ʵ����...
* ����: zhuzhiqiang
* ����ʱ��: 2009-4-3
* ����޸�ʱ��: 2009-4-27
*/

#ifndef _DEBUG_H
#define _DEBUG_H

//����
#define OPEN_DEBUGPRINT
#define OPEN_ASSERTLOG
//#define OPEN_DEBUGMODE

/************/
#define LOGTYPE_CLOSE			0  //�ر�
#define LOGTYPE_ALARM			1  //�澯
#define LOGTYPE_SHORT			2  //�����Ϣ
#define LOGTYPE_DOWNLINK		3  //����ͨ����Ϣ
#define LOGTYPE_UPLINK			4  //����ͨ����Ϣ
#define LOGTYPE_DATA			5  //���ݴ�ӡ��Ϣ
#define LOGTYPE_DEBUG			6  //���Դ�ӡ��Ϣ
#define LOGTYPE_TEST			10 //���Դ�ӡ

#define LOGITF_STDIO			0   //��׼�������
#define LOGITF_ETHER			1   //��̫��
#define LOGITF_PIPE				2   //�ܵ��ļ�
#define LOGITF_SVRCOMM		3   //����ͨ��//��ӡ������

#define ERROR_QRCODETIMEOUT		1   //��ά�����
#define ERROR_QRCODEUNKNOWN		2   //δ֪��ά��

//��ӡ���е�����Ϣ
void PrintLog(int type, const char *format, ...);
void PrintHexLog(int type, const unsigned char *buf, int len);

void SetLogType(int type);
int GetLogType(void);
int GetLogInterface(void);
void SetLogInterface(int itf);

//���Դ�ӡ,��ʽ���а治����
#ifdef OPEN_DEBUGPRINT
#define DebugPrint		      PrintLog
#else
#define DebugPrint(a, ...)
#endif

#ifdef OPEN_DEBUGMODE
#define DEBUGMODE
#endif

/****************/
//��ʽ���а汾������
#ifdef OPEN_ASSERTLOG

//#define PATH_ASSERTLOG		"/tmp/"
//��������������ʱʹ��,����Ϣд����־��
void PrintErrorLog(const char *format, ...);

#define ErrorLog(format...) { \
	PrintErrorLog("\n%s line %d:", __FILE__, __LINE__); \
	PrintErrorLog(format); }

#define AssertLog(cond, format...) { \
	if(cond) { \
		PrintErrorLog("\n%s line %d:", __FILE__, __LINE__); \
		PrintErrorLog(format); \
	} \
}

#define AssertLogReturn(cond, rtn, format...) { \
	if(cond) { \
		PrintErrorLog("\n%s line %d:", __FILE__, __LINE__); \
		PrintErrorLog(format); \
		return rtn; } \
}

#define AssertLogReturnVoid(cond, format...) { \
	if(cond) { \
		PrintErrorLog("\n%s line %d:", __FILE__, __LINE__); \
		PrintErrorLog(format); \
		return; } \
}

#else /*OPEN_ASSERTLOG*/

#define ErrorLog(format...)
#define AssertLog(cond, format...)
#define AssertLogReturn(cond, rtn, format...) { if(cond) return rtn; }
#define AssertLogReturnVoid(cond, format...) { if(cond) return; }

#endif

//����ʼ��������δִ��
struct _init_flag_t {
	const char *name;
	int flag;
};

#define DECLARE_INIT_FUNC(func) \
	static struct _init_flag_t _initflag_##func \
	__attribute__((__used__)) \
	__attribute__((section("_init_flag"), unused)) \
	= {#func, 0}

#define SET_INIT_FLAG(func) _initflag_##func.flag = 1

void CheckInitFlag(void);
extern int   exitflag;
/**���Ժ���**/
#define SMALLCPY_INLINE		1
#ifdef SMALLCPY_INLINE
static inline void smallcpy(void *dest, const void *src, unsigned int len)
{
	unsigned int i;
	unsigned char *pdest = (unsigned char *)dest;
	const unsigned char *psrc = (const unsigned char *)src;

	for(i=0; i<len; i++) *pdest++ = *psrc++;
}

#else
void smallcpy(void *dest, const void *src, unsigned int len);
#endif

#endif /*_DEBUG_H*/

