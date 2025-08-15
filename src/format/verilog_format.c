
#include <stdio.h>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include <stdlib.h>
#include <string.h>

static char **split(const char *source, char flag);
static char *search(char *arr,int flag);
static char *h2b(char *arr, int flag);
static int getIndexOfSigns(char ch);
static long hexToDec(char *source);

extern int verilogformat(char *inputfile,char *outputfile)
{
    char c[100000];//读取文件的每一行的数据
    char infile[10], outfile[10];//文件名
    char *s1,*s2,*s3,*s4,*s5;//判断变量，是否含有对应符号
    char **p1, **p6;
    char *h[2];//16进制中间变量
    char *b1[4196], *b2[4196];//16进制数里的中间变量
    char *p3[10000];//中间变量
    char *p4[2];//用来储存冒号前后的数
    char *p5[10000];//最后输出的文本
    int p4_n[1], num[4196], eq=0, su,h1[1],*b[10000],bn=0,ll=0;
    //printf("输入文件名为");
    //scanf("%s",infile);
    //printf("%s", infile);
    //*infile = *filename;
    // infile = argv;
    //printf("输出文件名为");
    //scanf("%s",outfile);
    if(fopen(inputfile, "r")==NULL){
        printf("file not found\n");
    }
    else{
    FILE *fptr = fopen(inputfile, "r");
    FILE *out = fopen(outputfile, "w");
    while (fgets(c,sizeof(c),fptr) != NULL)
    {
        //fputs(c, out);
        p1 = split(c, ' ');//分割完毕
        if(strstr(c, "assign"))
        {
            if(strstr(c, "{")||strstr(c, ":"))
        {
            if(strstr(c, "?")==NULL)//无？
            {
            for (int i = 0,j=1,k=1; p1[i] != NULL;i++)
            {
                s1 = strstr(p1[i], "{");
                s2 = strstr(p1[i], "}");
                s4 = strstr(p1[i], ":");
                s5 = strstr(p1[i], "'h");
                if (s1!=NULL||s2!=NULL)//有{}
                {
                    s1 = NULL;
                    s2 = NULL;
                }
                else{
                    p3[j-1] = p1[i];
                    if(s5!=NULL)//是16进制
                    {
                        char **hh;
                        char s[50];
                        ll = 0;
                        hh = split(p1[i], ';');
                        h[0] = h2b(hh[0], 1);
                        h[1] = h2b(hh[0], 2);
                        sprintf(s,"0x%s",h[1]);
                        h1[0] = atoi(h[0]);       
                        int n;                   
                        n = hexToDec(h[1]);                       
                        for (int i=0;n>0;n=n/2,i++)
                        {
                            *b[i]=n % 2;                          
                            bn=i;
                        }
                        for (int i = 0;i<=bn;i++)
                        {
                            if(b[bn-i]==0){
                                b1[i] = "1'b0";
                            }
                            if(b[bn-i]==1){
                                b1[i] = "1'b1";
                            }                         
                        }
                        for (int i = 1, l=0;i<=h1[0];i++)
                        {
                            
                            if((bn+1)<=h1[0]-i)
                            {
                                b2[i] = "1'b0";
                                ll++;
                            }
                            else
                            {
                                b2[i] = b1[l];
                                l++;
                                ll++;
                            }                       
                            
                        }
                        for (int i = 1;i<=ll;i++)
                            {
                                p5[k - 1] = b2[i];                               
                                su = k;
                                k++;
                            }
                        for (int i = 0;b[i]!=NULL;i++)
                            {
                                b[i] = NULL;
                            }
                        for (int i = 0;b1[i]!=NULL;i++)
                            {
                                b1[i] = NULL;
                            }
                        for (int i = 0;b2[i]!=NULL;i++)
                            {
                                b2[i] = NULL;
                            }
                    }                 
                    if(s4!=NULL)//有冒号
                    {                       
                        for (int i = 0; i < 3;i++)
                        {
                            p4[i] = search(p3[j - 1], i+1);
                        }
                        p4_n[0]= atoi(p4[1]);//取出冒号前数字
                        p4_n[1]= atoi(p4[2]);//取出冒号后数字
                        int s;
                        for (s = 0; s <= p4_n[0] - p4_n[1];)
                        {
                            num[s] = p4_n[0] - s;                           
                            s++;
                        }                   
                        //int nn = sizeof(num) / sizeof(num[0]);
                        //char a[nn][250]; //a[0]代表的是:12
                        char a[4196];
                        for (int i = 0;i<s;i++)//包装
                        {
                            sprintf(a, "%d", num[i]);
                            //num_String(num[i], a[i]);                        
                            p4[0] = search(p3[j - 1], 1);                          
                            p4[0] = strcat(p4[0], "[");                           
                            p5[k - 1] = strcat(p4[0], a);                            
                            p5[k - 1] = strcat(p5[k - 1], "]");                                                   
                            su = k;
                            k++;
                        }
                                              
                    }
                    if(s5==NULL&&s4==NULL)
                    {
                    p5[k - 1] = p3[j - 1];
                    p6=split(p5[k-1],',');//去除逗号
                    p6 = split(p6[0], ';');
                    p5[k - 1] = p6[0];
                    if( s3 = strstr(p5[k-1], "="))
                    {
                        eq = k - 1;
                        s3 = NULL;
                    }
                    su = k;
                    k = k + 1;
                    }
                    j++;
                    s1 = NULL;
                    s2 = NULL;
                    s4 = NULL;
                    s5 = NULL;
                }                
            }
            for (int i = 1;i<su/2 ;i++)
            {
               fputs("assign ", out);
               fputs(p5[i], out);
               fputs(" = ", out);
               fputs(p5[eq+i], out);
               fputs(";", out);
               fputs("\n", out);
            }
            for (int i = 0; p5[i] != NULL;i++)
            {
                p5[i] = NULL;
            }
            for (int i = 0; p3[i] != NULL;i++)
            {
                p3[i] = NULL;
            }
            for (int i = 0; p4[i] != NULL;i++)
            {
                p4[i] = NULL;
            }
        }
        else
        {
            fputs(c, out);
        }
        }
        else
        {
            fputs(c, out);
        }
    }
        else
        {
            fputs(c, out);
        }
    } 
    fclose(fptr);
    fclose(out);
    //system("pause");   //以便在退出程序前调用系统的暂停命令暂停命令行
    //return 0;
}}
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
