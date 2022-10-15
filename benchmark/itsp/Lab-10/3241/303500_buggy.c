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

int main(){
    char *s1,*s2;
    int l1,l2,i,j,c=0;
    scanf("%d ",&l1);
    s1=(char *)malloc(l1*sizeof(char));
    scanf("%s\n%d",s1,&l2);
    s2=(char *)malloc(l2*sizeof(char));
    scanf("%s",s2);
   
    return 0 ; }