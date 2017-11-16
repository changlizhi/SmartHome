// compress.cpp : Defines the entry point for the console application.
//

#include <stdio.h>
#include <memory.h>
#include <stdlib.h>

/**************************************************************
LZARI.C -- A Data Compression Program
(tab = 4 spaces)
***************************************************************
4/7/1989 Haruhiko Okumura
Use, distribute, and modify this program freely.
Please send me your improved versions.
PC-VAN		SCIENCE
NIFTY-Serve	PAF01022
CompuServe	74050,1022
**************************************************************/
#include <stdio.h>
unsigned char *rbuff,*dbuff;
unsigned long   InputLength;
unsigned long    CurrentInputPtr;       /* count of get memory data */
unsigned long   CurrentOutputPtr;       /* count of put memory data */

unsigned long int  textsize , codesize, printcount ;

int  getmemc(void);
void putmemc(int ret);

/********** Bit I/O **********/

static unsigned int  buffer2 = 0, mask2 = 128;

void PutBit(int bit)  /* Output one bit (bit = 0,1) */
{
	//	static unsigned int  buffer = 0, mask = 128;
	
	if (bit) buffer2 |= mask2;
	if ((mask2 >>= 1) == 0) {
		putmemc(buffer2);
		buffer2 = 0;  mask2 = 128;  codesize++;
	}
}

void FlushBitBuffer(void)  /* Send remaining bits */
{
	int  i;
	
	for (i = 0; i < 7; i++) PutBit(0);
}

static unsigned int  buffer1, mask1 = 0;
int GetBit(void)  /* Get one bit (0 or 1) */
{
	//	static unsigned int  buffer, mask = 0;
	
	if ((mask1 >>= 1) == 0) {
		buffer1 = getmemc();  
		mask1 = 128;
	}
	return ((buffer1 & mask1) != 0);
}

/********** LZSS with multiple binary trees **********/

#define N		 4096	/* size of ring buffer */
#define F		   60	/* upper limit for match_length */
#define THRESHOLD	2   /* encode string into position and length
if match_length is greater than this */
#define NIL			N	/* index for root of binary search trees */

unsigned char  text_buf[N + F - 1];	/* ring buffer of size N,
with extra F-1 bytes to facilitate string comparison */
int		match_position, match_length,  /* of longest match.  These are
set by the InsertNode() procedure. */
lson[N + 1], rson[N + 257], dad[N + 1];  /* left & right children &
parents -- These constitute binary search trees. */

void InitTree(void)  /* Initialize trees */
{
	int  i;
	
	/* For i = 0 to N - 1, rson[i] and lson[i] will be the right and
	   left children of node i.  These nodes need not be initialized.
	   Also, dad[i] is the parent of node i.  These are initialized to
	   NIL (= N), which stands for 'not used.'
	   For i = 0 to 255, rson[N + i + 1] is the root of the tree
	   for strings that begin with character i.  These are initialized
	   to NIL.  Note there are 256 trees. */
	
	for (i = N + 1; i <= N + 256; i++) 
		rson[i] = NIL;	/* root */
	for (i = 0; i < N; i++) 
		dad[i] = NIL;	/* node */
}

void InsertNode(int r)
/* Inserts string of length F, text_buf[r..r+F-1], into one of the
trees (text_buf[r]'th tree) and returns the longest-match position
and length via the global variables match_position and match_length.
If match_length = F, then removes the old node in favor of the new
one, because the old one will be deleted sooner.
Note r plays double role, as tree node and position in buffer. */
{
	int  i, p, cmp, temp;
	unsigned char  *key;
	
	cmp = 1;  key = &text_buf[r];  p = N + 1 + key[0];
	rson[r] = lson[r] = NIL;  match_length = 0;
	for ( ; ; ) {
		if (cmp >= 0) {
			if (rson[p] != NIL) p = rson[p];
			else {  rson[p] = r;  dad[r] = p;  return;  }
		} else {
			if (lson[p] != NIL) p = lson[p];
			else {  lson[p] = r;  dad[r] = p;  return;  }
		}
		for (i = 1; i < F; i++)
			if ((cmp = key[i] - text_buf[p + i]) != 0)  break;
			if (i > THRESHOLD) {
				if (i > match_length) {
					match_position = (r - p) & (N - 1);
					if ((match_length = i) >= F) break;
				} else if (i == match_length) {
					if ((temp = (r - p) & (N - 1)) < match_position)
						match_position = temp;
				}
			}
	}
	dad[r] = dad[p];  lson[r] = lson[p];  rson[r] = rson[p];
	dad[lson[p]] = r;  dad[rson[p]] = r;
	if (rson[dad[p]] == p) rson[dad[p]] = r;
	else                   lson[dad[p]] = r;
	dad[p] = NIL;  /* remove p */
}

void DeleteNode(int p)  /* Delete node p from tree */
{
	int  q;
	
	if (dad[p] == NIL) return;  /* not in tree */
	if (rson[p] == NIL) q = lson[p];
	else if (lson[p] == NIL) q = rson[p];
	else {
		q = lson[p];
		if (rson[q] != NIL) {
			do {  q = rson[q];  } while (rson[q] != NIL);
			rson[dad[q]] = lson[q];  dad[lson[q]] = dad[q];
			lson[q] = lson[p];  dad[lson[p]] = q;
		}
		rson[q] = rson[p];  dad[rson[p]] = q;
	}
	dad[q] = dad[p];
	if (rson[dad[p]] == p) rson[dad[p]] = q;
	else                   lson[dad[p]] = q;
	dad[p] = NIL;
}

/********** Arithmetic Compression **********/

/*  If you are not familiar with arithmetic compression, you should read
I. E. Witten, R. M. Neal, and J. G. Cleary,
Communications of the ACM, Vol. 30, pp. 520-540 (1987),
from which much have been borrowed.  */

#define M   15

/*	Q1 (= 2 to the M) must be sufficiently large, but not so
large as the unsigned long 4 * Q1 * (Q1 - 1) overflows.  */

#define Q1  (1UL << M)
#define Q2  (2 * Q1)
#define Q3  (3 * Q1)
#define Q4  (4 * Q1)
#define MAX_CUM (Q1 - 1)

#define N_CHAR  (256 - THRESHOLD + F)
/* character code = 0, 1, ..., N_CHAR - 1 */

unsigned long int  low = 0, high = Q4, value = 0;
int  shifts = 0;  /* counts for magnifying low and high around Q2 */
int  char_to_sym[N_CHAR], sym_to_char[N_CHAR + 1];
unsigned int
sym_freq[N_CHAR + 1],  /* frequency for symbols */
sym_cum[N_CHAR + 1],   /* cumulative freq for symbols */
position_cum[N + 1];   /* cumulative freq for positions */

void StartModel(void)  /* Initialize model */
{
	int ch, sym, i;
	
	sym_cum[N_CHAR] = 0;
	for (sym = N_CHAR; sym >= 1; sym--) {
		ch = sym - 1;
		char_to_sym[ch] = sym;  sym_to_char[sym] = ch;
		sym_freq[sym] = 1;
		sym_cum[sym - 1] = sym_cum[sym] + sym_freq[sym];
	}
	sym_freq[0] = 0;  /* sentinel (!= sym_freq[1]) */
	position_cum[N] = 0;
	for (i = N; i >= 1; i--)
		position_cum[i - 1] = position_cum[i] + 10000 / (i + 200);
	/* empirical distribution function (quite tentative) */
	/* Please devise a better mechanism! */
}

void UpdateModel(int sym)
{
	int i, c, ch_i, ch_sym;
	
	if (sym_cum[0] >= MAX_CUM) {
		c = 0;
		for (i = N_CHAR; i > 0; i--) {
			sym_cum[i] = c;
			c += (sym_freq[i] = (sym_freq[i] + 1) >> 1);
		}
		sym_cum[0] = c;
	}
	for (i = sym; sym_freq[i] == sym_freq[i - 1]; i--) ;
	if (i < sym) {
		ch_i = sym_to_char[i];    ch_sym = sym_to_char[sym];
		sym_to_char[i] = ch_sym;  sym_to_char[sym] = ch_i;
		char_to_sym[ch_i] = sym;  char_to_sym[ch_sym] = i;
	}
	sym_freq[i]++;
	while (--i >= 0) sym_cum[i]++;
}

static void Output(int bit)  /* Output 1 bit, followed by its complements */
{
	PutBit(bit);
	for ( ; shifts > 0; shifts--) PutBit(! bit);
}

void EncodeChar(int ch)
{
	int  sym;
	unsigned long int  range;
	
	sym = char_to_sym[ch];
	range = high - low;
	high = low + (range * sym_cum[sym - 1]) / sym_cum[0];
	low +=       (range * sym_cum[sym    ]) / sym_cum[0];
	for ( ; ; ) {
		if (high <= Q2) Output(0);
		else if (low >= Q2) {
			Output(1);  low -= Q2;  high -= Q2;
		} else if (low >= Q1 && high <= Q3) {
			shifts++;  low -= Q1;  high -= Q1;
		} else break;
		low += low;  high += high;
	}
	UpdateModel(sym);
}

void EncodePosition(int position)
{
	unsigned long int  range;
	
	range = high - low;
	high = low + (range * position_cum[position    ]) / position_cum[0];
	low +=       (range * position_cum[position + 1]) / position_cum[0];
	for ( ; ; ) {
		if (high <= Q2) Output(0);
		else if (low >= Q2) {
			Output(1);  low -= Q2;  high -= Q2;
		} else if (low >= Q1 && high <= Q3) {
			shifts++;  low -= Q1;  high -= Q1;
		} else break;
		low += low;  high += high;
	}
}

void EncodeEnd(void)
{
	shifts++;
	if (low < Q1) 
		Output(0);  
	else 
		Output(1);
	FlushBitBuffer();  /* flush bits remaining in buffer */
}

int BinarySearchSym(unsigned int x)
/* 1      if x >= sym_cum[1],
N_CHAR if sym_cum[N_CHAR] > x,
i such that sym_cum[i - 1] > x >= sym_cum[i] otherwise */
{
	int i, j, k;
	
	i = 1;  j = N_CHAR;
	while (i < j) {
		k = (i + j) / 2;
		if (sym_cum[k] > x) 
			i = k + 1;  
		else j = k;
	}
	return i;
}

int BinarySearchPos(unsigned int x)
/* 0 if x >= position_cum[1],
N - 1 if position_cum[N] > x,
i such that position_cum[i] > x >= position_cum[i + 1] otherwise */
{
	int i, j, k;
	
	i = 1;  j = N;
	while (i < j) {
		k = (i + j) / 2;
		if (position_cum[k] > x) i = k + 1;  else j = k;
	}
	return i - 1;
}

void StartDecode(void)
{
	int i;
	
	for (i = 0; i < M + 2; i++)
		value = 2 * value + GetBit();
}

int DecodeChar(void)
{
	int	 sym, ch;
	unsigned long int  range;
	
	range = high - low;
	sym = BinarySearchSym((unsigned int)
		(((value - low + 1) * sym_cum[0] - 1) / range));
	high = low + (range * sym_cum[sym - 1]) / sym_cum[0];
	low +=       (range * sym_cum[sym    ]) / sym_cum[0];
	for ( ; ; ) {
		if (low >= Q2) {
			value -= Q2;  low -= Q2;  high -= Q2;
		} else if (low >= Q1 && high <= Q3) {
			value -= Q1;  low -= Q1;  high -= Q1;
		} else if (high > Q2) break;
		low += low;  high += high;
		value = 2 * value + GetBit();
	}
	ch = sym_to_char[sym];
	UpdateModel(sym);
	return ch;
}

int DecodePosition(void)
{
	int position;
	unsigned long int  range;
	
	range = high - low;
	position = BinarySearchPos((unsigned int)
		(((value - low + 1) * position_cum[0] - 1) / range));
	high = low + (range * position_cum[position    ]) / position_cum[0];
	low +=       (range * position_cum[position + 1]) / position_cum[0];
	for ( ; ; ) {
		if (low >= Q2) {
			value -= Q2;  low -= Q2;  high -= Q2;
		} else if (low >= Q1 && high <= Q3) {
			value -= Q1;  low -= Q1;  high -= Q1;
		} else if (high > Q2) break;
		low += low;  high += high;
		value = 2 * value + GetBit();
	}
	return position;
}

/********** Encode and Decode **********/

void Encode(void)
{
	int  i, c, len, r, s, last_match_length;
	
	*(long *)dbuff=(long)textsize;
	codesize += sizeof textsize;
    textsize = 0;
	StartModel();  
	InitTree();
	s = 0;  r = N - F;
	for (i = s; i < r; i++) text_buf[i] = ' ';
	for (len = 0; len < F && (c = getmemc()) != EOF; len++)
		text_buf[r + len] = c;
	textsize = len;
	for (i = 1; i <= F; i++)
		InsertNode(r - i);
	InsertNode(r);
	do {
		if (match_length > len) 
			match_length = len;
		if (match_length <= THRESHOLD) 
		{
			match_length = 1;  
			EncodeChar(text_buf[r]);
		} else {
			EncodeChar(255 - THRESHOLD + match_length);
			EncodePosition(match_position - 1);
		}
		last_match_length = match_length;
		for (i = 0; i < last_match_length &&
			(c = getmemc()) != EOF; i++) 
		{
			DeleteNode(s);  
			text_buf[s] = c;
			if (s < F - 1) 
				text_buf[s + N] = c;
			s = (s + 1) & (N - 1);
			r = (r + 1) & (N - 1);
			InsertNode(r);
		}
#if PRINTMSG
		if ((textsize += i) > printcount) {
			printf("%12ld\r", textsize);  
			printcount += 1024;
		}
#endif
		while (i++ < last_match_length) 
		{
			DeleteNode(s);
			s = (s + 1) & (N - 1);
			r = (r + 1) & (N - 1);
			if (--len) 
				InsertNode(r);
		}
	} while (len > 0);
	EncodeEnd();
#if PRINTMSG
	printf("In : %lu bytes\n\r", textsize);
	printf("Out: %lu bytes\n\r", codesize);
	printf("Out/In: %.3f\n\r", (double)codesize / textsize);
#endif
}

void Decode(void)
{
	int  i, j, k, r, c;
	unsigned long int  count;
	memcpy(&textsize,rbuff,4);
	StartDecode();  
	StartModel();
	for (i = 0; i < N - F; i++) 
		text_buf[i] = ' ';
	r = N - F;
	for (count = 0; count < textsize; ) 
	{
		c = DecodeChar();
		if (c < 256) 
		{
			putmemc(c);
			text_buf[r++] = c;
			r &= (N - 1);  
			count++;
		} 
		else 
		{
			i = (r - DecodePosition() - 1) & (N - 1);
			j = c - 255 + THRESHOLD;
			for (k = 0; k < j; k++) {
				c = text_buf[(i + k) & (N - 1)];
				putmemc(c);
			             text_buf[r++] = c;
						 r &= (N - 1);  
						 count++;
			}
		}
#if PRINTMSG
		if (count > printcount) {
			printf("%12lu\r", count);  
			printcount += 1024;
		}
        
	}
	printf("%12lu\n\r", count);
#else
        }
#endif
}




/********get memory data************/
int  getmemc(void)
{
	if(CurrentInputPtr<InputLength)
		return *(rbuff+CurrentInputPtr++);
	else
	{
		CurrentInputPtr++;
		return EOF;
	}
}

/********put memory data************/

void putmemc(int ret)
{
	
	*(dbuff+CurrentOutputPtr)=ret;
	CurrentOutputPtr++;
	
}
void InitCompress(void)
{
	memset(text_buf,0,sizeof(text_buf));
	match_position=match_length=0;
	
	memset(lson,0,sizeof(lson));
	memset(rson,0,sizeof(rson));
	memset(dad,0,sizeof(dad));
	low = 0;
	high = Q4;
	value = 0;
	shifts = 0;
	memset(char_to_sym,0,sizeof(char_to_sym));
	memset(sym_to_char,0,sizeof(sym_to_char));
	memset(sym_freq,0,sizeof(sym_freq));
	memset(sym_cum,0,sizeof(sym_cum));
	memset(position_cum,0,sizeof(position_cum));
	buffer2 = 0;
	mask2 = 128;
	buffer1 = 0;
	mask1 = 0;
}

//Src:要压缩文件首地址
//Len:要压缩的长度
//Dst:压缩后地址，包括4bytes头
int Compress(unsigned char * Src ,unsigned long  Len ,unsigned char * Dst)    /*压缩函数*/
{
	if (Len==0) 
		return 0;	
	rbuff=Src;
	InputLength=Len;
	dbuff=Dst;
	CurrentInputPtr=0;
	CurrentOutputPtr=4;
	codesize = 0;
	printcount = 0;
	textsize = InputLength;
	InitCompress();
	Encode();
	return CurrentOutputPtr;
}

//Src:压缩后文件首地址，包括4bytes头
//Len:压缩后长度
//Dst:解压后地址
int UnCompress(unsigned char * Src ,unsigned long Len ,unsigned char * Dst)  /*解压缩函数*/
{
	if (Len==0) 
		return 0;
	rbuff=Src;
	InputLength=Len;
	dbuff=Dst;
	CurrentInputPtr=4;
	CurrentOutputPtr=0;
	codesize = 0;
	printcount = 0;
	textsize = 0;
	InitCompress();
	Decode();
	return CurrentOutputPtr;
}

#if 0
#define REPEAT 1

void main1(int argc,char *argv[])
{
	unsigned  char *SrcData;
	unsigned  char *DstData;
	FILE  *infile, *outfile;
	int SrcLen,OutLen,i;
	
	
	
	
	
	//	for(i=0;i<30;i++)
	{
#if 1
		printf("按任意键开始压缩\n\r");
		//压缩文件
		infile  = fopen(argv[1], "rb");
		outfile=fopen(argv[2],"wb");
		if(infile==NULL)
		{
			printf("Error1,cannot open file!");
			return;
		}
		fseek(infile,0,SEEK_END);
		SrcLen=ftell(infile);
		fseek(infile,0,SEEK_SET);
		SrcData=(unsigned char *)malloc(SrcLen);
		if(NULL==SrcData)
		{
			printf("Error2,cannot open file!");
			printf("SrcLen=%lu\n\r" ,SrcLen);
			return;
		}
		DstData=(unsigned char *)malloc(SrcLen);
		if(NULL==DstData)
		{
			printf("Error3,cannot open file!");
			return;
		}
		printf("压缩 %s 长度 %d\n\r" ,argv[1],SrcLen);
		fread(SrcData,SrcLen,1,infile);
		
		for(i=0;i<REPEAT;i++)
			OutLen=Compress(SrcData,SrcLen,DstData);
		fwrite(DstData,OutLen,1,outfile);
		
		fclose(infile);
		fclose(outfile);
		
		free(SrcData);
		free(DstData);
		printf("按任意键开始解压\n\r");
		getchar();
#endif
		//解压文件
		infile  = fopen(argv[2], "rb");
		outfile=fopen(argv[3],"wb");
		if(infile==NULL)
		{
			printf("Error1,cannot open file!");
			return;
		}
		fseek(infile,0,SEEK_END);
		SrcLen=ftell(infile);
		fseek(infile,0,SEEK_SET);
		SrcData=(unsigned char *)malloc(SrcLen);
		if(NULL==SrcData)
		{
			printf("Error2,cannot open file!");
			printf("SrcLen=%lu\n\r" ,SrcLen);
			return;
		}
		fread(SrcData,SrcLen,1,infile);
		memcpy(&OutLen,SrcData,4);
		DstData=(unsigned char *)malloc(OutLen);
		
		if(NULL==DstData)
		{
			printf("Error3,cannot open file!");
			return;
		}
		printf("解压文件 %s 长度 %d \n\r" ,argv[2],SrcLen);
		
		for(i=0;i<REPEAT;i++)
			OutLen=UnCompress(SrcData,SrcLen,DstData);
		fwrite(DstData,OutLen,1,outfile);
		
		fclose(infile);
		fclose(outfile);
		
		free(SrcData);
		free(DstData);
		getchar();
	}
}

#endif

#define CRC16_POLY    0x1021
const unsigned short g_crc_tab[256] = {
	0x0000, 0x1021, 0x2042, 0x3063, 0x4084, 0x50A5, 0x60C6, 0x70E7,
	0x8108, 0x9129, 0xA14A, 0xB16B, 0xC18C, 0xD1AD, 0xE1CE, 0xF1EF,
	0x1231, 0x0210, 0x3273, 0x2252, 0x52B5, 0x4294, 0x72F7, 0x62D6,
	0x9339, 0x8318, 0xB37B, 0xA35A, 0xD3BD, 0xC39C, 0xF3FF, 0xE3DE,
	0x2462, 0x3443, 0x0420, 0x1401, 0x64E6, 0x74C7, 0x44A4, 0x5485,
	0xA56A, 0xB54B, 0x8528, 0x9509, 0xE5EE, 0xF5CF, 0xC5AC, 0xD58D,
	0x3653, 0x2672, 0x1611, 0x0630, 0x76D7, 0x66F6, 0x5695, 0x46B4,
	0xB75B, 0xA77A, 0x9719, 0x8738, 0xF7DF, 0xE7FE, 0xD79D, 0xC7BC,
	0x48C4, 0x58E5, 0x6886, 0x78A7, 0x0840, 0x1861, 0x2802, 0x3823,
	0xC9CC, 0xD9ED, 0xE98E, 0xF9AF, 0x8948, 0x9969, 0xA90A, 0xB92B,
	0x5AF5, 0x4AD4, 0x7AB7, 0x6A96, 0x1A71, 0x0A50, 0x3A33, 0x2A12,
	0xDBFD, 0xCBDC, 0xFBBF, 0xEB9E, 0x9B79, 0x8B58, 0xBB3B, 0xAB1A,
	0x6CA6, 0x7C87, 0x4CE4, 0x5CC5, 0x2C22, 0x3C03, 0x0C60, 0x1C41,
	0xEDAE, 0xFD8F, 0xCDEC, 0xDDCD, 0xAD2A, 0xBD0B, 0x8D68, 0x9D49,
	0x7E97, 0x6EB6, 0x5ED5, 0x4EF4, 0x3E13, 0x2E32, 0x1E51, 0x0E70,
	0xFF9F, 0xEFBE, 0xDFDD, 0xCFFC, 0xBF1B, 0xAF3A, 0x9F59, 0x8F78,
	0x9188, 0x81A9, 0xB1CA, 0xA1EB, 0xD10C, 0xC12D, 0xF14E, 0xE16F,
	0x1080, 0x00A1, 0x30C2, 0x20E3, 0x5004, 0x4025, 0x7046, 0x6067,
	0x83B9, 0x9398, 0xA3FB, 0xB3DA, 0xC33D, 0xD31C, 0xE37F, 0xF35E,
	0x02B1, 0x1290, 0x22F3, 0x32D2, 0x4235, 0x5214, 0x6277, 0x7256,
	0xB5EA, 0xA5CB, 0x95A8, 0x8589, 0xF56E, 0xE54F, 0xD52C, 0xC50D,
	0x34E2, 0x24C3, 0x14A0, 0x0481, 0x7466, 0x6447, 0x5424, 0x4405,
	0xA7DB, 0xB7FA, 0x8799, 0x97B8, 0xE75F, 0xF77E, 0xC71D, 0xD73C,
	0x26D3, 0x36F2, 0x0691, 0x16B0, 0x6657, 0x7676, 0x4615, 0x5634,
	0xD94C, 0xC96D, 0xF90E, 0xE92F, 0x99C8, 0x89E9, 0xB98A, 0xA9AB,
	0x5844, 0x4865, 0x7806, 0x6827, 0x18C0, 0x08E1, 0x3882, 0x28A3,
	0xCB7D, 0xDB5C, 0xEB3F, 0xFB1E, 0x8BF9, 0x9BD8, 0xABBB, 0xBB9A,
	0x4A75, 0x5A54, 0x6A37, 0x7A16, 0x0AF1, 0x1AD0, 0x2AB3, 0x3A92,
	0xFD2E, 0xED0F, 0xDD6C, 0xCD4D, 0xBDAA, 0xAD8B, 0x9DE8, 0x8DC9,
	0x7C26, 0x6C07, 0x5C64, 0x4C45, 0x3CA2, 0x2C83, 0x1CE0, 0x0CC1,
	0xEF1F, 0xFF3E, 0xCF5D, 0xDF7C, 0xAF9B, 0xBFBA, 0x8FD9, 0x9FF8,
	0x6E17, 0x7E36, 0x4E55, 0x5E74, 0x2E93, 0x3EB2, 0x0ED1, 0x1EF0,
};

unsigned short cal_crc(unsigned char *pbuf, unsigned long count)
{
	unsigned short temp = 0;

	if(0 == count) return 0;

	while ( count-- != 0 )
	{
		temp = ( temp<<8 ) ^ g_crc_tab[ ( temp>>8 ) ^ *pbuf++ ];
	}
    
	return temp;
}

typedef struct {
	int len;
	unsigned short magic;
	unsigned short crc;
} ziphead_t;

typedef struct {
	unsigned short magic;
	unsigned short crc;
} filehead_t;

int main(int argc, char* argv[])
{
	int bcompress = 1;
	unsigned int magic;
	unsigned  char *SrcData;
	unsigned  char *DstData, *pOffset;
	FILE  *infile, *outfile;
	int SrcLen,OutLen;
	ziphead_t *pHeadZip;
	filehead_t *pHeadFile;

	if(5 != argc) {
		printf("compress z(or u) magic srcfile dstfile\n");
		return 1;
	}

	if('z' == *argv[1]) bcompress = 1;
	else if('u' == *argv[1]) bcompress = 0;
	else { 
		printf("compress z(or u) magic srcfile dstfile\n");
		return 1;
	}

	SrcData = DstData = NULL;

	magic = atoi(argv[2]);

	infile  = fopen(argv[3], "rb");
	outfile = fopen(argv[4],"wb");
	if((infile==NULL) || (outfile == NULL)) {
		printf("Error1,cannot open file!");
		if(NULL != infile) fclose(infile);
		if(NULL != outfile) fclose(outfile);
		return 1;
	}

	if(bcompress) {
		fseek(infile,0,SEEK_END);
		SrcLen=ftell(infile);
		fseek(infile,0,SEEK_SET);

		SrcData=(unsigned char *)malloc(SrcLen+4);
		if(NULL==SrcData) {
			printf("Error2, memory malloc error!");
			goto MARK_CHKERR;
		}
		DstData=(unsigned char *)malloc(SrcLen+16);
		if(NULL==DstData) {
			printf("Error2, memory malloc error!");
			goto MARK_CHKERR;
		}

		fread(&SrcData[4],SrcLen,1,infile);
		pHeadFile = (filehead_t *)SrcData;
		pHeadFile->magic = magic;
		pHeadFile->crc = cal_crc(&SrcData[4], SrcLen);
		SrcLen += 4;

		pOffset = DstData + 8;
		OutLen=Compress(SrcData,SrcLen,pOffset);

		pHeadZip = (ziphead_t *)DstData;
		pHeadZip->magic = magic;
		pHeadZip->len = OutLen;
		pHeadZip->crc = cal_crc(pOffset, OutLen);
		fwrite(DstData,OutLen+8,1,outfile);
		
		fclose(infile);
		fclose(outfile);
		
		free(SrcData);
		free(DstData);

		printf("compress end OK\n");
	}
	else {
		fseek(infile,0,SEEK_END);
		SrcLen=ftell(infile);
		fseek(infile,0,SEEK_SET);

		SrcData=(unsigned char *)malloc(SrcLen);
		if(NULL==SrcData) {
			printf("Error2, memory malloc error!");
			goto MARK_CHKERR;
		}
		fread(SrcData,SrcLen,1,infile);

		pHeadZip = (ziphead_t *)SrcData;
		if(magic != pHeadZip->magic) {
			printf("magic error\n");
			goto MARK_CHKERR;
		}

		if(SrcLen != (pHeadZip->len+8)) {
			printf("len error\n");
			goto MARK_CHKERR;
		}

		if(pHeadZip->crc != cal_crc(&SrcData[8], pHeadZip->len)) {
			printf("crc error\n");
			goto MARK_CHKERR;
		}

		pOffset = SrcData + 8;

		memcpy(&OutLen,pOffset,4);

		DstData=(unsigned char *)malloc(OutLen);
		if(NULL==DstData) {
			printf("Error2, memory malloc error!");
			goto MARK_CHKERR;
		}
		
		OutLen=UnCompress(pOffset,SrcLen,DstData);

		if(OutLen <= 4) {
			printf("len error!\n");
			goto MARK_CHKERR;
		}

		pHeadFile = (filehead_t *)DstData;
		if(magic != pHeadFile->magic) {
			printf("unzip magic error\n");
			goto MARK_CHKERR;
		}
		if(pHeadFile->crc != cal_crc(&DstData[4], OutLen-4)) {
			printf("unzip crc error\n");
			goto MARK_CHKERR;
		}

		fwrite(&DstData[4],OutLen-4,1,outfile);
		
		fclose(infile);
		fclose(outfile);
		
		free(SrcData);
		free(DstData);

		printf("uncompress end OK\n");
	}
	
	return 0;

MARK_CHKERR:
	if(NULL != SrcData) free(SrcData);
	if(NULL != DstData) free(DstData);
	fclose(infile);
	fclose(outfile);
	return 1;
}

