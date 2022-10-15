/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
age", ExpOutput:"eag", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
edcba", ExpOutput:"No Answer", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
ahgf", ExpOutput:"fagh", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
czyx", ExpOutput:"xcyz", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"4
aaaa", ExpOutput:"No Answer", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam", ExpOutput:"labexma", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abtsrqp", ExpOutput:"apbqrst", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
prrrs", ExpOutput:"prrsr", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abdczyx", ExpOutput:"abdxcyz", Output:""
*/
#include <stdio.h>
#include <stdlib.h>

int main(){
    //Fill this area with your code.
    int i,n,j,count=0;
    char str[100],ch,ch1;
    scanf("%d\n",&n);
    scanf("%s",str);
    for(i=n-1;i>0;i--)
    {
        ch=str[i];
        for(j=i-1;j>=0;j--)
        {
            if(str[j]>ch)
            {
                ch1=str[j];
                str[j]=str[i];
                str[i]=ch1;
                count++;
                break;
            }
        }
        if(count!=0)
        break;
    }
    return 0;
}