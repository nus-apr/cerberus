/*numPass=4, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"defabc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"aprograprog"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"rhello-@prhello-@"
Verdict:ACCEPTED, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"abab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"ohellohel"
Verdict:ACCEPTED, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"mmingproga"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"cabca"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"bab"
Verdict:ACCEPTED, Visibility:0, Input:"a", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
int slen(char str[]){int i=0;
    while(str[i]!='\0'){
        i++;
    }
    
   return i; 
}
void swap(char a[],int n){
    int i;
    char tmp;
   if(!(n%2)){ for( i=0;i<n/2;i++){
        tmp=a[i];
        a[i]=a[n/2+i];
        a[n/2+i]=tmp;
    }
       
   }else{ for( i=0;i<n-1/2;i++){
        tmp=a[i];
        a[i]=a[n/2+i];
        a[(n+1)/2+i]=tmp;
    }
       
   }
   
    a[n]='\0';
}
int main() {
char str[100];
scanf("%s",str);


swap(str,slen(str));
printf("%s",str);
	return 0;
}