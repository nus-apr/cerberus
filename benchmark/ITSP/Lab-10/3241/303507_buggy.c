/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4 hehe
6 hehehe", ExpOutput:"he", Output:"he"
Verdict:ACCEPTED, Visibility:1, Input:"4 abab
8 abababab", ExpOutput:"abab", Output:"abab"
Verdict:ACCEPTED, Visibility:1, Input:"4 heeh
6 hehehe", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"5 hello
6 hihihi", ExpOutput:"", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 a
5 aaaaa", ExpOutput:"a", Output:"a)"
*/
#include <stdio.h>
#include <stdlib.h>
int main(){
    int a,b,i,j,l=0,x=1;
    scanf("%d",&a);
    char str1[a];
    scanf("%s",str1);
    scanf("%d",&b);
    char str2[b];
    scanf("%s",str2);
    char check[a];
    for(i=0;i<a;i++){
        if(str1[i]==str2[i]&&str1[i]==str2[a+i]){
            check[i]=str1[i];
        }else{
            check[i]='\0';
            break;
        }
    }
    for(j=0;j<a;j++){
        if(str1[j]==str2[j]){
            x=1;
        }else{
            x=0;
            break;
        }
    }
    if(x==1){
        printf("%s",check);
    }
	return 0 ; 
}