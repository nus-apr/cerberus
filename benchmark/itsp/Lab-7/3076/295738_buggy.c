/*numPass=4, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"defabc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"ammingprogr"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"rogrammerhello-@p"
Verdict:ACCEPTED, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"abab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"odearhell"
Verdict:ACCEPTED, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"mmingproga"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"cdzab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"bca"
Verdict:ACCEPTED, Visibility:0, Input:"a", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
   
int main() {
    char str[100];
    int i,n=0;
    scanf("%s",str);
    for(i=0;str[i]!='\0';i++);
    if(i%2==0){
        for(n=i/2;n<i;n++){
            printf("%c",str[n]);
        }
        for(n=0;n<i/2;n++){
            printf("%c",str[n]);
        }
    }
    else{
        for(n=(i-1)/2;n<i;n++){
            printf("%c",str[n]);
        }
        for(n=0;n<(i-1)/2;n++){
            printf("%c",str[n]);
        }
    }
    
    
	return 0;
}