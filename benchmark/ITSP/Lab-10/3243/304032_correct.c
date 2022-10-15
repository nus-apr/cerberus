/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"3
age", ExpOutput:"eag", Output:"eag"
Verdict:ACCEPTED, Visibility:1, Input:"5
edcba", ExpOutput:"No Answer", Output:"No Answer"
Verdict:ACCEPTED, Visibility:1, Input:"4
ahgf", ExpOutput:"fagh", Output:"fagh"
Verdict:ACCEPTED, Visibility:1, Input:"4
czyx", ExpOutput:"xcyz", Output:"xcyz"
Verdict:ACCEPTED, Visibility:0, Input:"4
aaaa", ExpOutput:"No Answer", Output:"No Answer"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam", ExpOutput:"labexma", Output:"labexma"
Verdict:ACCEPTED, Visibility:0, Input:"7
abtsrqp", ExpOutput:"apbqrst", Output:"apbqrst"
Verdict:ACCEPTED, Visibility:0, Input:"5
prrrs", ExpOutput:"prrsr", Output:"prrsr"
Verdict:ACCEPTED, Visibility:0, Input:"7
abdczyx", ExpOutput:"abdxcyz", Output:"abdxcyz"
*/
#include <stdio.h>
#include <stdlib.h>

int main(){
    //Fill this area with your code.
    int i,n,j,count=0,k;
    char str[100],ch,ch1;
    scanf("%d\n",&n);
    scanf("%s",str);
    for(i=n-1;i>0;i--)
    {
        ch=str[i];
        for(j=i-1;j>=0;j--)
        {
            if(str[j]<ch)
            {
                ch1=str[j];
                str[j]=str[i];
                str[i]=ch1;
                count++;
                k=j;
                break;
            }
        }
        if(count!=0)
        break;
    }
    for(i=k+1;i<n;i++)
    {
        ch=str[i];
        for(j=i+1;j<n;j++)
        {
            if(ch>str[j])
            {
                ch1=str[j];
                str[j]=str[i];
                str[i]=ch1;
            }
        }    
    }
    if(count==0)
    printf("No Answer");
    else
    printf("%s",str);
    return 0;
}