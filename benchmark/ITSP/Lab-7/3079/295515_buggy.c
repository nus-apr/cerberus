/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcde 
bcd ", ExpOutput:"adcbe", Output:"0 4 adcbe"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcde 
acb ", ExpOutput:"abcde", Output:"0 1 2 3 4 abcde"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdebcd 
bcd ", ExpOutput:"adcbedcb", Output:"0 4 adcbedcb"
Verdict:WRONG_ANSWER, Visibility:1, Input:"qwerty
t", ExpOutput:"qwerty", Output:"0 1 2 3 5 qwerty"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manually
all", ExpOutput:"manullay", Output:"0 1 2 3 7 manullay"
Verdict:WRONG_ANSWER, Visibility:0, Input:"iamesrever
esrever", ExpOutput:"iamreverse", Output:"0 1 2 iamreverse"
Verdict:WRONG_ANSWER, Visibility:0, Input:"youdogaredog
dog", ExpOutput:"yougodaregod", Output:"0 1 2 6 7 8 yougodaregod"
Verdict:WRONG_ANSWER, Visibility:0, Input:"ghhghghhghghhg
hhg", ExpOutput:"gghhhgghhhgghh", Output:"0 4 5 9 10 gghhhgghhhgghh"
*/
#include <stdio.h>

int length(char s[]); //returns the length of string

int main(){
    char s1[100],s2[100];
    int i,l1,l2,j,k,c,l=0,p=0;
    scanf("%s\n",s1);
    scanf("%s",s2);
    l1=length(s1); //stores the length of s1 
    l2=length(s2); //stores the length of s2
    char s3[l2+1],s4[l1+1];
    //reverses the string s2;
    for(i=0,j=l2-1;i<l2;i++,j--){
        s3[i]=s2[j];}
        s3[l2]='\0';
    //changing the string
    for(i=0;i<l1;i++){
        k=i;
        c=0; //counts the number of matching characters
        //checks if s2 is present in s1
        for(j=0;j<l2;j++){
            if(s1[i++]==s2[j])
               c++;}
        //if it is present then it stores the revresed substring
        if(c==l2){
           p=0;
           for(l=k;l<k+l2;l++){
               s4[l]=s3[p];
               p++;}
            i--;}
        //otherwise it stores the original charcters
        else{
            printf("%d ",k);
            i=k;
           s4[i]=s1[i];}}
    printf("%s",s4);
    return 0;}
 
int length(char s[100]){
    int i=0;
    while(s[i]!='\0'){
        i++;}
    return i;}     
    