/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"14", ExpOutput:"17
", Output:"17"
Verdict:ACCEPTED, Visibility:1, Input:"24", ExpOutput:"29
", Output:"29"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"2
", Output:"2"
Verdict:ACCEPTED, Visibility:1, Input:"68", ExpOutput:"71
", Output:"71"
Verdict:ACCEPTED, Visibility:0, Input:"99", ExpOutput:"101
", Output:"101"
Verdict:ACCEPTED, Visibility:0, Input:"150", ExpOutput:"151
", Output:"151"
Verdict:ACCEPTED, Visibility:0, Input:"200", ExpOutput:"211
", Output:"211"
*/
#include<stdio.h>

int check_prime(int num)
{
int i,j,ctr;
if (num==1) i=2;
else{
for(i=num;;i++)
{ctr=0;
    for(j=2;j<num;j++)
    {if(i%j==0) ctr++;
        
    }if (ctr==0) break;
}}
return i;
}

int main(){
    
int n,p;
scanf("%d",&n);
p=check_prime(n);
printf("%d",p);
return 0;
}