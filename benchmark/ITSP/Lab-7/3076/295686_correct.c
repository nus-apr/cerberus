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
    char str[100], laststr[100];//x is to make the string small
    int c=getchar();
    int m=0,x;
    for(m=0;c!=-1;m++)
    {
        str[m]=c;
        c=getchar();
    }
    int n;
    for(n=0;n<((m+1)/2);n++)
    {
        x=n+((m+1)/2);
        laststr[n]=str[x];
    }if(m%2!=0){
        laststr[n-1]=str[n-1];
        
    }
    for(;(n<m);n++){
        
        x=n-((m+1)/2);
        laststr[n]=str[x];

    }
        
     for(int l=0;l<m;l++)
     {
         printf("%c",laststr[l]);
    }
	return 0;
}