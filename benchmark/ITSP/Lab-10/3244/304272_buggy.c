/*numPass=8, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"5
abcde", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:1, Input:"8
pqrsabcd", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:1, Input:"4
azpg", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"8
aaaazzzz", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:0, Input:"6
abczpq", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"6
abcpqz", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"8
acegikmo", ExpOutput:"Good String", Output:"Good String"
Verdict:WRONG_ANSWER, Visibility:0, Input:"ab", ExpOutput:"Good String", Output:"Not Good String"
*/
#include <stdio.h>
#include <stdlib.h>
int mod(int a){
    if(a<0){
        int b=-a;
        return b;
    }
    else{
        return a;
    }
}

int main(){
    int n,i,cnt=0;
    scanf("%d",&n);/*input*/
    char *s,*r;
    s=(char*)malloc((n+1)*sizeof(char));/*n+1 due to exta null char*/ 
    scanf("%s",s);
    r=(char*)malloc((n+1)*sizeof(char));
    for(i=0;i<n;i++){
        *(r+i)=*(s+(n-1-i));
    }
if(n==1){
 printf("Good String");
}

  else{  for(i=1;i<=n;i++){
        int k1=mod(*(s+i)-*(s+(i-1)));
        int k2=mod(*(r+i)-*(r+(i-1)));
if(k1==k2){
    cnt++;
}
        }
    if(cnt==(n-1)){
        printf("Good String");
    }
    else{
        printf("Not Good String");
    }}
    return 0;
}