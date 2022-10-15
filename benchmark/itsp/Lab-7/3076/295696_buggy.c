/*numPass=3, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"defabc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"mmingprogr"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"ogrammerhello-@p0C"
Verdict:ACCEPTED, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"abab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"dearhell"
Verdict:ACCEPTED, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"mmingproga"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"dzab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"ca"
Verdict:WRONG_ANSWER, Visibility:0, Input:"a", ExpOutput:"a", Output:""
*/
#include <stdio.h>
int strl(char str[]){//funtion for lenth of string
    int i=0;
    while(*(str++)!='\0'){
        i++;
    }
    return i;
}
int main() {
	char str[100];int i;
	scanf("%s",str);
    	int n=strl(str);//length of string
	char str1[50],str2[50];

    if(n%2==0){	//if n is even 
        for(i=0;i<n/2;i++){
	    str1[i]=str[i];
        }
	    for(i=0;i<n/2;i++){    
	    str2[i]=str[n/2+n%2+i];
       }
    }
   else {//if n is odd
       for(i=0;i<n/2;i++){
        str1[i]=str[i];
       }
       for(i=0;i<=n/2;i++){
        str2[i]=str[n/2+1+i];
        
       }
    }
	printf("%s%s",str2,str1);


	return 0;
}