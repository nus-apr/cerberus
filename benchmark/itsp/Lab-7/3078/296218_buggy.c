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
    char A[100];
    int i,j;
    int count=0;
    scanf("%s",A);
    for(i=0;A[i]!='\0';i++)
    {
        count++;
    }
    for(j=0;j<count;j++)
    {
        A[j]=A[j]+A[j]-'a'+1;
    }
    printf("%s",A);
	return 0;
}