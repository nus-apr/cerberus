/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"98bdfhjl
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"120tvxz
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"121zxvt
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:"0n
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"108xxx
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"119htjjnx
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"97zbbpbxxxbhhjhnjlnfbljl
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"108xxxxx
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"105rrlrdrxrnx
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
	printf("%d",str[1]);
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