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
int gcd(int a,int b){
    if(a<b){
        int temp=a;
        a=b;
        b=temp;
    }
    if(a%b==0)
    return b;
    else
    return gcd(b,a%b);
}


int main(){
int n1,i,count=0;
scanf("%d",&n1);
char str1[n1];
scanf("%s",str1);
int n2;
scanf("%d",&n2);
char str2[n2];
scanf("%s",str2);
for(i=0;i<n2;i++){
    if(str1[0]!=str2[0])
    printf("");
    if(str2[i]==str1[i%n1])
        count++;
    
    
}
if(count==n2){
    if(n2%n1==0)
    printf("%s",str1);
    else{
        for(i=0;i<gcd(n1,n2);i++){
        printf("%c",str1[i]);}
    }
    
}

	return 0 ; 
}