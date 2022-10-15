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
void swap_str(char a,char b){
    char temp;
    temp=b;
     b=a;
     a=temp;
}
int main() {
    char str[100];
	int j,i=0,k;
	while(str[i]!='\0'){
	    scanf("%s",&str[i]);
	    i++;
	}
	scanf("%s",&str[i]);
	for(j=0;j<i/2;j++){
	    char temp=str[j];
	    str[j]=str[j+(i+1)/2];
	    str[j+(i+1)/2]=temp;
	}
	//for(k=0;k<i+1;k++){
	    printf("%s",str);
	//}
	return 0;
}