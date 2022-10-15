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

int main(){
    char *str;
    char rvrse[1000];
    int n,c=0;
    scanf("%d",&n);
    str=(char*)malloc((n+1)*sizeof(char));
    scanf("%s",str);
    for(int i=0;i<n;i++)
    {
        rvrse[i]=str[n-1-i];
    }
    for(int i=1;i<n;i++)
    {
        if((str[i]-str[i-1]==rvrse[i]-rvrse[i-1])||((str[i]-str[i-1]           )+(rvrse[i]-rvrse[i-1])==0)){

        c++;}
    }
    if(c==n-1&&n!=0)
    printf("Good String");
    else if(n!=0)
    printf("Not Good String");
    else if(n==0)
    printf("Good String");
    return 0;
}