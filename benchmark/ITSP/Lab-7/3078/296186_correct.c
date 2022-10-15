/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:ACCEPTED, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"tvxz"
Verdict:ACCEPTED, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"zxvt"
Verdict:ACCEPTED, Visibility:1, Input:"t", ExpOutput:"n", Output:"n"
Verdict:ACCEPTED, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xxx"
Verdict:ACCEPTED, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"htjjnx"
Verdict:ACCEPTED, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zbbpbxxxbhhjhnjlnfbljl"
Verdict:ACCEPTED, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"xxxxx"
Verdict:ACCEPTED, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rrlrdrxrnx"
*/
#include <stdio.h>

int main() {
	char s[200];
	scanf("%s",s);
	int i=0;
	while(s[i] != '\0')
	{
	    s[i] = s[i] + s[i] - 'a'+1;
	    if(s[i] > 'z'){
	        s[i] = s[i] - 26;
	    }
	    else if(s[i] == 'z')
	    {
	        s[i] = 'z';
	    }
	   
	    
	    i++;
	}
	int j=0;
	while(s[j] != '\0')
	{
	    printf("%c",s[j]);
        j++;
	}
	
	
	
}