/*numPass=1, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"bc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"rogrgpammin"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"ello-@prhrogramme"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"b"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"ellrhodea"
Verdict:WRONG_ANSWER, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"roga"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"bzacd"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"cab"
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

int main() {
    int temp,i,len;
    char str[100];
    scanf("%s",str);
        len=str_len(str);
        
        for(i=0;i<len/2;i++){
            temp=str[i];
            str[i]=str[i+len/2];
            str[i+len/2]=temp;
        }
          for(i=0;i<len/2;i++){
            temp=str[i];
            str[i]=str[i+len/2+1];
            str[i+len/2+1]=temp;
          
        } 
        printf("%s",str);
        
        
	return 0;
}