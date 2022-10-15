/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:""
*/
#include <stdio.h>

int main() {
    int i=0;
    char stri[100],stro[i];
    
    for(i=0;i<=100;i++)
   { 
    scanf("%c",&stri[i]);
    while(stri[i]!='\0')
    {
        return 0;
    }
   
    stro[i]=stri[i]+stri[i]-96;
    if(stro[i]>122)
    {
        stro[i]=stro[i]-122+96;
         printf("%c",stro[i]);
    }
    else
    printf("%c",stro[i]);
   }
  
	return 0;
}