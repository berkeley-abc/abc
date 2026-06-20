#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "ioAbc.h"
#include "base/main/mainInt.h"
#include "aig/saig/saig.h"
#include "proof/abs/abs.h"
#include "sat/bmc/bmc.h"

#ifdef WIN32
#include <process.h> 
#define unlink _unlink
#else
#include <unistd.h>
#endif

static char **split(const char *source, char flag);
static char *search(char *arr,int flag);
static char *h2b(char *arr, int flag);
static int getIndexOfSigns(char ch);
static long hexToDec(char *source);
static int verilog_format();
extern int glo_fMapped;


extern void Format_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "verilog_format","verilog_format",verilog_format,0);
}
extern void Format_End( Abc_Frame_t * pAbc )
{
	
}

static int verilog_format( Abc_Frame_t * pAbc, int argc, char ** argv)
{
    Abc_Ntk_t * pNtk;
    char * inputfile,* outputfile;
    int fCheck, fBarBufs;
    int c;

    fCheck = 1;
    fBarBufs = 0;
    glo_fMapped = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {

            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if ( argc != globalUtilOptind + 2 )
    {
        goto usage;
    }
    // get the input file name
    inputfile  = argv[globalUtilOptind];
    outputfile = argv[globalUtilOptind+1];
    extern int verilogformat(char *filename, char *outputfile);
    verilogformat(inputfile,outputfile);
    return 0;
usage:
    fprintf( pAbc->Err, "usage: read_verilog <inputfile> <outputfile>\n" );
    fprintf( pAbc->Err, "\t               read  Verilog\n" );
    fprintf( pAbc->Err, "\tinputfile    : the name of a file to read\n" );
    fprintf( pAbc->Err, "\toutputfile   : the name of a file to write\n" );
    return 1;

    
}
char *h2b(char *arr,int flag)
{
    char **q1,**q2;
    char *q3[2];
    q1 = split(arr, '\'');
    q2 = split(arr, 'h');
    q3[0] = q1[0];
    q3[1] = q2[1];
    if(flag==1){
        return q3[0];
    }
    if(flag==2){
        return q3[1];
    }
}
char *search(char *arr,int flag)//拆分带：项目
{
    char **q1,**q2;
    char *q3[2];
    q1 = split(arr, '[');
    q2 = split(q1[1], ']');
    q2 = split(q2[0], ':');
    q3[0] = q1[0];
    q3[1] = q2[0];
    q3[2] = q2[1];
   if(flag==1)
       return q3[0];
    if(flag==2)
       return q3[1];
    if(flag==3)
       return q3[2];
}
char **split(const char *source, char flag)
{
    char **pt;
    int j, n = 0;
    int count = 1;
    int len = strlen(source);
    // 动态分配一个 *tmp，静态的话，变量len无法用于下标
    char *tmp = (char*)malloc((len + 1) * sizeof(char));
    tmp[0] = '\0';

    for (int i = 0; i < len; ++i)
    {
        if (source[i] == flag && source[i+1] == '\0')
            continue;
        else if (source[i] == flag && source[i+1] != flag)
            count++;
    }
    // 多分配一个char*，是为了设置结束标志
    pt = (char**)malloc((count+1) * sizeof(char*));

    count = 0;
    for (int i = 0; i < len; ++i)
    {
        if (i == len - 1 && source[i] != flag)
        {
            tmp[n++] = source[i];
            tmp[n] = '\0';  // 字符串末尾添加空字符
            j = strlen(tmp) + 1;
            pt[count] = (char*)malloc(j * sizeof(char));
            strcpy(pt[count++], tmp);
        }
        else if (source[i] == flag)
        {
            j = strlen(tmp);
            if (j != 0)
            {
                tmp[n] = '\0';  // 字符串末尾添加空字符
                pt[count] = (char*)malloc((j+1) * sizeof(char));
                strcpy(pt[count++], tmp);
                // 重置tmp
                n = 0;
                tmp[0] = '\0';
            }
        }
        else
            tmp[n++] = source[i];
    }    
    // 释放tmp
	free(tmp);
    // 设置结束标志
    pt[count] = NULL;
    return pt;
}

long hexToDec(char *source)
{
    long sum = 0;
    long t = 1;
    int i, len;
 
    len = strlen(source);
    for(i=len-1; i>=0; i--)
    {
        sum += t * getIndexOfSigns(*(source + i));
        t *= 16;
    }  
 
    return sum;
} 
/* 返回ch字符在sign数组中的序号 */
int getIndexOfSigns(char ch)
{
    if(ch >= '0' && ch <= '9')
    {
        return ch - '0';
    }
    if(ch >= 'A' && ch <='F') 
    {
        return ch - 'A' + 10;
    }
    if(ch >= 'a' && ch <= 'f')
    {
        return ch - 'a' + 10;
    }
    return -1;
}
