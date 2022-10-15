/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4 hehe
6 hehehe", ExpOutput:"he", Output:"he"
Verdict:ACCEPTED, Visibility:1, Input:"4 abab
8 abababab", ExpOutput:"abab", Output:"abab"
Verdict:ACCEPTED, Visibility:1, Input:"4 heeh
6 hehehe", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"5 hello
6 hihihi", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1 a
5 aaaaa", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
#include <stdlib.h>
int fn(char s1[],char s2[],int a){
    int x,i;
    for(i=0;i<a;i++){
    if(s1[i]==s2[i])
        x=1;
        else
        x=0;
        
        if(x==0)
        break;
    }
    return x;
}

int main(){
    int m,n;
    scanf("%d",&m);
    char str1[m];
    scanf("%s",str1);
    scanf("%d",&n);
    char str2[n];
    scanf("%s",str2);
    int i;
    if(fn(str1,str2,m)==1){
        for(i=0;i<m;i++){
            if(str1[i]==str2[i+m]){
                printf("%c",str1[i]);
            }
        }
    }
	return 0 ; 
}