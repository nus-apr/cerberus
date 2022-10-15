/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"14", ExpOutput:"17
", Output:"25"
Verdict:WRONG_ANSWER, Visibility:1, Input:"24", ExpOutput:"29
", Output:"25"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"2
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"68", ExpOutput:"71
", Output:"121"
Verdict:WRONG_ANSWER, Visibility:0, Input:"99", ExpOutput:"101
", Output:"121"
Verdict:WRONG_ANSWER, Visibility:0, Input:"150", ExpOutput:"151
", Output:"169"
Verdict:WRONG_ANSWER, Visibility:0, Input:"200", ExpOutput:"211
", Output:"289"
*/
#include<stdio.h>

int check_prime(int num)
{
int i,j,ctr;

for(i=num;;i++)
{ctr=0;
    for(j=1;j<=num;j++)
    {if(i%j==0) ctr++;
        
    }if (ctr==2) break;
}
return i;
}

int main(){
    
int n,p;
scanf("%d",&n);
p=check_prime(n);
printf("%d",p);
return 0;
}