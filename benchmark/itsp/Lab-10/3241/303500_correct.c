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

int common_divisor(int ,int);//calculates the greatest common divisor given numbers
int check(char *,char *,int,int);//checks whether the gcd is the only occuring word in the string

int main(){
    char *s1,*s2,*s3;
    int l1,l2,i,gcd,a,b;
    scanf("%d ",&l1);
    s1=(char *)malloc(l1*sizeof(char));
    scanf("%s\n%d",s1,&l2);
    s2=(char *)malloc(l2*sizeof(char));
    scanf("%s",s2);
    gcd=common_divisor(l1,l2);
    s3=(char *)malloc(gcd*sizeof(char));
    for(i=0;i<gcd;i++)
       s3[i]=s1[i];
    a=check(s1,s3,l1,gcd);
    b=check(s2,s3,l2,gcd);
    if(a&&b)
      printf("%s",s3);
    else
      printf("");
    return 0;}
    
int common_divisor(int a,int b){
    int c;
    if(a<b){
      c=a;
      a=b;
      b=c;}
    while(a%b!=0){
        a=a%b;
        c=a;
        a=b;
        b=c;}
    return b;}
    
int check(char *s,char *s1,int l1,int gcd){
    int i,j,c=0;
    for(i=0;i<l1;i=i+gcd)
       for(j=0;j<gcd;j++)
          if(s[i+j]==s1[j])
            c++;
    if(c==l1)
      return 1;
    else
      return 0;}    