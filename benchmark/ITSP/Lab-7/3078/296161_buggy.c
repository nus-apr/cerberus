/*numPass=3, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"acegik"
Verdict:ACCEPTED, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"tvxz"
Verdict:ACCEPTED, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"zxvt"
Verdict:ACCEPTED, Visibility:1, Input:"t", ExpOutput:"n", Output:"n"
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"wwx"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"htijnx"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"yabpawwxaggignilnealil"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"xwwxw"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rqlqcqwqnx"
*/
#include <stdio.h>

int main() {
    int i;
	char str[100];     // creatindg a string of 100 elements.
	char b;
	scanf("%s",str);
	//printf("%s",str);
	for(i=0;str[i]!=0;i++)
	{
	
        if (str[i]>'m')     // m lies in middle of alphabetical order.
        {
            b=str[i]+str[i]-'a'-25;
        }
        else 
        {
            b=str[i]+str[i]-'a';
        }
        printf("%c",b);
    }
	return 0;
}