/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"abcdef(vA@v@@l"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"wxyzmA@m@@l"
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"zyxwNA@N@@l"
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:"tGA@F@@l"
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"lly1A@1@@l"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"qwertyX{{A@8{{@@l"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"manuallyaddedtestcasesA@!@@l"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"yllyl(4A@4@@l"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"visibilityA@@@l"
*/
#include <stdio.h>

int main() {char a[101];
int i;
for(i=0;i<101;i++)
{scanf("%c",&a[i]);
printf("%c",a[i]);}
return 0;    
}