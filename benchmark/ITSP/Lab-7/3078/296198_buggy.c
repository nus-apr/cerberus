/*numPass=1, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"uwy{"
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"{ywu"
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:"o"
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xxy"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"iujkoy"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zbcqbxxybhhjhojmofbmjm"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"yxxyx"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"srmrdrxroy"
*/
#include <stdio.h>

int main() {
       char str[100];
       scanf("%s",str);
       int i;
	   for(i=0;str[i]!='\0';i++)
	   {
	      if(str[i]+str[i]-96<=122)
	      {
	       printf("%c",str[i]+str[i]-96);   
	      }
	      else printf("%c",str[i]+str[i]-96-25);
	   }
	return 0;
}