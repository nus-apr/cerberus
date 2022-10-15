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
	char str[100],c;
	int i,l=0,d=0;
	for(i=0;i<100;i++)
	{
	    scanf("%c",&str[i]);
	}
	for(i=0;i<100;i++)
	{
	    if(str[i]>='a'&&str[i]<='z')
	    l++;
	    else
	    d++;
	}
 	for(i=0;i<l;i++)
 	{
 	    str[i]=(str[i])*2-96;
 	    if(str[i]>122)
 	    {
 	       str[i]=str[i]-122+96;
 	       printf("%c",str[i]);
 	    }
 	    else
 	    {
 	       printf("%c",str[i]);
 	    }
 	}
	return 0;
}