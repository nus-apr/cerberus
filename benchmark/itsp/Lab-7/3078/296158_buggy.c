/*numPass=1, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xx"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"j"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zb|bxxbhhjhjfbj"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"xxx"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rrdrxr"
*/
#include <stdio.h>

int main() {
    char lw[100];int i;
    for(i=0;lw[i]!='\0';i++)
    {
        scanf("%s",&lw[i]);
    }
     for(i=0;lw[i]!='\0';i++)
     {
         lw[i]=(lw[i]-97)+1+lw[i];
     }
     for(i=0;lw[i]!='\0';i++)
     {
         printf("%c",lw[i]);
     }
	return 0;
}