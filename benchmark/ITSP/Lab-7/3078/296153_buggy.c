/*numPass=1, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"]^_`"
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"`_^]"
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:"Z"
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xx_"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"W]jXZ_"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zbT[bxx_bhhjhZjYZfbYjY"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"_xx_x"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"\rYrdrxrZ_"
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
 	    c=(str[i])*2-96;
 	    if(c>122)
 	    {
 	       c=str[i]-122+96;
 	       printf("%c",c);
 	    }
 	    else
 	    {
 	       printf("%c",c);
 	    }
 	}
	return 0;
}