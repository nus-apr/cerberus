/*numPass=2, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 hehe
6 hehehe", ExpOutput:"he", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 abab
8 abababab", ExpOutput:"abab", Output:""
Verdict:ACCEPTED, Visibility:1, Input:"4 heeh
6 hehehe", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"5 hello
6 hihihi", ExpOutput:"", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 a
5 aaaaa", ExpOutput:"a", Output:""
*/
#include <stdio.h>
#include <stdlib.h>
int fn(char s1[],char s2[]){
    if(s1[1]==s2[1]&&s1[2]==s2[2]&&s1[3]==s2[3]&&s1[4]==s2[4])
        return 1;
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
    if(fn(str1,str2)==1){
        for(i=0;i<m;i++){
            if(str1[i]==str2[i+m]){
                printf("%c",str1[i]);
            }
        }
    }
	return 0 ; 
}