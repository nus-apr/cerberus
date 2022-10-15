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

int str_len(char str[]){//function
    int i=0;//initionalaztion
    while (str[i]!='\0'){//loop
        i++;
    }
    return i;
}

int main() {//main function
    int temp,i,len;//int value
    char str[100];//charactar array
    scanf("%s",str);
        len=str_len(str);//function calling
        
        //if(len%2==0){
        for(i=0;i<len/2;i++){
             if(len%2==0){

            temp=str[i];
            str[i]=str[i+len/2];
            str[i+len/2]=temp;
        }
        }
       // else(len%2!=0){
            
        for(i=0;i<len/2;i++){
            if(len%2!=0){
            temp=str[i];
            str[i]=str[i+len/2+1];
            str[i+len/2+1]=temp;
        }  
        } 
        printf("%s",str);
        
        
	return 0;
}