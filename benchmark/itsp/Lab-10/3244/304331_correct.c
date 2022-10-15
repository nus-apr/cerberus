/*numPass=9, numTotal=9
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
Verdict:ACCEPTED, Visibility:0, Input:"ab", ExpOutput:"Good String", Output:"Good String"
*/
#include <stdio.h>
#include <stdlib.h>

int function(int n,char *s){
    char *r;
    int i,count=0;
    r=(char*)malloc((n+1)*sizeof(char));
    for(i=0;i<n;i++){
        r[i]=s[n-i-1];//reverse string
    }
    for(i=1;i<n;i++){
    if((s[i]-s[i-1])==(r[i]-r[i-1])||(s[i]-s[i-1])==(-1)*(r[i]-r[i-1])){
        count=count+1;
    }
    }
    return count;
}
int main(){
    int n;
    scanf("%d\n", &n);
    char *s;
    s=(char*)malloc((n+1)*sizeof(char));//dynamic memory allocation
    scanf("%s\n", s);
    if(n==0){
        printf("Good String");
        return 0;
    }
    if(function(n,s)==(n-1)){
        printf("Good String");
    }
    else{
        printf("Not Good String");
    }
    return 0;
}