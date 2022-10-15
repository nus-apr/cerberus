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
    int n;
    scanf("%d",&n);
    char *s=(char*)malloc(n*sizeof(char));
    char *r=(char*)malloc(n*sizeof(char));
    int ch;
    ch=getchar();//reads newline
    ch=getchar();
    int i=0;
    while(i<n)
    {
      s[i]=ch;
      r[n-i-1]=ch;
      ch=getchar();
      i++;
    }
    int j=1;
    int count=1;
    if(n==0||n==1){printf("Good String");}
    else{
        while(j<=n-1)
        {
            if(s[j]-s[j-1]==r[j]-r[j-1]||s[j]-s[j-1]==r[j-1]-r[j])
            {
                count++;
            }
            j++;
        }
            if(count==n){printf("Good String");}
            else{printf("Not Good String");}
        }
    return 0;
}