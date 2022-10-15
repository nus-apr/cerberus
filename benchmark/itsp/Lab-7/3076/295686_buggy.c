/*numPass=1, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"abc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"aprogr"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"rhello-@p"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"ab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"`Johell"
Verdict:WRONG_ANSWER, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"Jproga"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"cab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"ba"
Verdict:ACCEPTED, Visibility:0, Input:"a", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>

int main() {
    char str[100], laststr[100];
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
        x=n+((m+1/2));
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