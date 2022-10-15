/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl
"
Verdict:ACCEPTED, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"tvxz
"
Verdict:ACCEPTED, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"zxvt
"
Verdict:ACCEPTED, Visibility:1, Input:"t", ExpOutput:"n", Output:"n
"
Verdict:ACCEPTED, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xxx
"
Verdict:ACCEPTED, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"htjjnx
"
Verdict:ACCEPTED, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zbbpbxxxbhhjhnjlnfbljl
"
Verdict:ACCEPTED, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"xxxxx
"
Verdict:ACCEPTED, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rrlrdrxrnx
"
*/
#include <stdio.h>

int main() {
	char str[100];
	int i=0,count=0;
	gets(str);
	while(str[i]!='\0')
	{
	    count=count+1;
	    i++;
	}
	for(i=0;i<count;i++)
	{
	    str[i]=str[i]+str[i]-96;
	    if(str[i]>122)
	    {
	        str[i]=str[i]-26;
	    }
	}
	puts(str);
	return 0;
}