/*numPass=3, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:""
Verdict:ACCEPTED, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"tvxz"
Verdict:ACCEPTED, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"zxvt"
Verdict:ACCEPTED, Visibility:1, Input:"t", ExpOutput:"n", Output:"n"
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"x"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"htjnx"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"bpxnlnll"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"xx"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rlnx"
*/
#include <stdio.h>

int main() 
{
    int ch[100];
    int i,c=0;
	for(i=0;i<100;i++)
	{
	    ch[i]=getchar();
	    if(ch[i]>=97&&ch[i]<=122)	
	    c++;
	}
	for(int j=0;j<c;j++)
	{
	    int a=ch[j]-96;
	    int k=ch[j]+a;
	    
	    if(k<=122)
	    {
	        printf("%c",ch[k]);
	    }
	    else
	    {
	        int d=k-122+96;
	        printf("%c",(char)d);
	    }
	}
	return 0;
}