/*numPass=1, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"fadebc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"amminprogrg"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"rogrammehello-@pr"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"baab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"odeahellr"
Verdict:WRONG_ANSWER, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"gpromminga"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"cdabz"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"bac"
Verdict:ACCEPTED, Visibility:0, Input:"a", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
int string_length(char a[]) 
{
   int i=0;
   while(a[i]!='\0')
   i++;
   return i;
}
int main() {
	char a[105];
	scanf("%s",a);
	int i,x=string_length(a);
	if(x%2==0) 
	{
	   for(i=0; i<x/2; i++) 
	   {
	       char c= a[i];
	       a[i]=a[x/2+i];
	       a[x/2+i]=c;
	   }    
	}
	for(i=0; i<((x-1)/2); i++) 
	{
	    char d=a[i];
	    a[i]=a[(x-1)/2+i];
	    a[(x-1)/2+i]=d;
	}
	printf("%s",a);

	return 0;
}