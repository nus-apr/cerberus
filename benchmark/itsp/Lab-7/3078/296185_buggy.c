/*numPass=1, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"-/13"
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"31/-"
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:"'"
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xx1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"!-j#'1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zb)bxx1bhhjh'j%'fb%j%"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"1xx1x"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"+r%rdrxr'1"
*/
#include <stdio.h>

void change(char str[]);
int main() 
{
    char str[101];
    scanf("%s",str);
    change(str);
    printf("%s",str);
	return 0;
}

void change(char str[])
{
    int i=0;
    while(str[i]!='\0')
    {
        str[i]+=((str[i]-'a')+1);
        if(str[i]>'z')
            str[i]-='a';
        i++;
    }
}