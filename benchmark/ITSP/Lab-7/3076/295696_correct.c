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
       str1[i]='\0';
       for(i=0;i<=n/2;i++){
        str2[i]=str[n/2+1+i];
        str2[n/2]=str[n/2];
       }str2[n/2+1]='\0';
    }
	printf("%s%s",str2,str1);


	return 0;
}