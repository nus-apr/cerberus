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

int main()
{
    int n,flag=0,position=-1;
    char *w;
    scanf("%d\n",&n);
    w=(char*)malloc(sizeof(char)*n);
    scanf("%s\n",w);
    char s[n];
    for(int i=0;i<n;i++)
    s[i]=w[i];
    for(int i=n-1;i>=0;i--)
        {
            for(int j=i-1;j>=0;j--)
                {
                    if(s[i]>s[j])
                        {
                            char c=s[j];
                            s[j]=s[i];
                            s[i]=c;
                            position=j;
                            flag++;
                            break;
                        }
                }
            if(flag!=0)
                {
                    for(int i=position+1;i<n;i++)
                        {
                            for(int j=i+1;j<n;j++)
                                {
                                    if(s[i]>s[j])
                                        {
                                            char c=s[j];
                                            s[j]=s[i];
                                            s[i]=c;                                                          }
                            }
                        }
                            printf("%s",s);break;
                }
                }
                if(flag==0)
                printf("No Answer");
            return 0;
    
    
}