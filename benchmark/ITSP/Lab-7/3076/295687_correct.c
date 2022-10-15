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

int str_len(char str[]){
    int i=0;
    while (str[i]!='\0'){
        i++;
    }
    return i;
}

void swap(int *a , int *b){
    int tmp;
    tmp=a;
    a=b;
    b=tmp;
}
int main() {
    int i,slength,tmp;
    char str[100];
    scanf("%s",str);
    slength=str_len(str);
    if (slength%2==0){
        for(i=0;i<(slength)/2;++i){
            tmp=str[i];
            str[i]=str[(slength/2)+i];
            str[(slength/2)+i]=tmp;
        }
    }
    else{
        for(i=0;i<(slength/2);++i){
            tmp=str[i];
            str[i]=str[(((slength)+1)/2)+i];
            str[(((slength)+1)/2)+i]=tmp;
        }
    }
    printf("%s",str);
	return 0;
}