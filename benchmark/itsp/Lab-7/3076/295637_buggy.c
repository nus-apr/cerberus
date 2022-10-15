/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"defabcdefabcdefabcdefabcdefabcdefabcdefabc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"mmingaprogrmmingaprogrmmingaprogrmmingaprogrmmingaprogrmmingaprogrmmingaprogrmmingaprogrmmingaprogrmmingaprogrmmingaprogrmmingaprogr"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"ogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@pogrammerrhello-@p"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"abababababababababab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"dearohelldearohelldearohelldearohelldearohelldearohelldearohelldearohelldearohelldearohell"
Verdict:WRONG_ANSWER, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"mmingprogammingprogammingprogammingprogammingprogammingprogammingprogammingprogammingprogammingprogammingproga"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"dzcabdzcabdzcabdzcabdzcabdzcab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"cbacbacbacba"
Verdict:WRONG_ANSWER, Visibility:0, Input:"a", ExpOutput:"a", Output:"aa"
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
	for(k=0;k<i+1;k++){
	    printf("%s",str);
	}
	return 0;
}