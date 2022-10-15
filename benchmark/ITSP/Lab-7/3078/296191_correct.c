/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:ACCEPTED, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"tvxz"
Verdict:ACCEPTED, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"zxvt"
Verdict:ACCEPTED, Visibility:1, Input:"t", ExpOutput:"n", Output:"n"
Verdict:ACCEPTED, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xxx"
Verdict:ACCEPTED, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"htjjnx"
Verdict:ACCEPTED, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zbbpbxxxbhhjhnjlnfbljl"
Verdict:ACCEPTED, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"xxxxx"
Verdict:ACCEPTED, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rrlrdrxrnx"
*/
#include <stdio.h>

int main() 
{
    int ch[100];
    int i,a,d,k,c=0;
	for(i=0;i<100;i++)
	{
	    ch[i]=getchar();
	    if(ch[i]>=97&&ch[i]<=122)	
	    c++;
	}
	for(int j=0;j<c;j++)
	{
	    a=ch[j]-96;
	    k=ch[j]+a;
	    
	    if(k<=122)
	    {
	        printf("%c",(char)k);
	    }
	    else
	    {
	        d=k-122+96;
	        printf("%c",(char)d);
	    }
	}
	return 0;
}