/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"defabc"
Verdict:ACCEPTED, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"mmingaprogr"
Verdict:ACCEPTED, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"ogrammerrhello-@p"
Verdict:ACCEPTED, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"abab"
Verdict:ACCEPTED, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"dearohell"
Verdict:ACCEPTED, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"mmingproga"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"dzcab"
Verdict:ACCEPTED, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"cba"
Verdict:ACCEPTED, Visibility:0, Input:"a", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>

int main() {
	char x[100]; char a;int len;char mid;
	int j;
    int i=0;
	while(x[i]!='\0')
	{
	    scanf("%s", x);
	    i++;
	}
	x[i+1]='\0';
	len=i;
	if(len%2==0)
	{
	    for(j=0;j<(len)/2;j++)
	    {
	        a=x[j];
	        x[j]=x[j+len/2];
	        x[j+len/2]=a;
	    }
	}    
	else
	    {   for(j=0;j<len/2;j++)
	            {
	                a=x[j];
	                x[j]=x[j+len/2+1];
	                x[j+len/2+1]=a;
	            }
	    }
	for(j=0;j<len;j++)
	{
	    printf("%c", x[j]);
	}
	return 0;
}