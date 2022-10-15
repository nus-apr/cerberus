/*numPass=2, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"abcdef"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"programming"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"hello-@programmer"
Verdict:ACCEPTED, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"abab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"hellodear"
Verdict:WRONG_ANSWER, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"progamming"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"abcdz"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"abc"
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

void swap(int a, int b){
    int temp;
    temp=a;
    a=b;
    b=temp;
}
int main() {
    int i,slength;
    char str[100];
    scanf("%s",str);
    slength=str_len(str);
    
    if (slength%2==0){
        for(i=0;i<(slength)/2;++i){
            swap(str[i],str[((slength)/2)+i]);
        }
    }
    else{
        for(i=0;i<(slength/2);++i){
            swap(str[i],str[((slength+1)/2)+i]);
        }
    }
    printf("%s",str);
	return 0;
}