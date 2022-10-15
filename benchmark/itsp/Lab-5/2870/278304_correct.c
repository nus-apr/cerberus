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

int check_prime(int num);
int check_prime(int num)
{
    int i,j,tmp;
    for(i=num;i>=num;i++)
    {
    for(j=2;j<i/2;j++)
    {
    tmp=1;
    if(i%j==0)
    {
        tmp=0;
        break;
    }
    }
    if(tmp==0)
    continue;
    if((tmp==1)&&(i>1))
    return i;
    }
}
    

int main()
{
    int N,x;
    scanf("%d",&N);
    x=check_prime(N);
    printf("%d",x);
    return 0;
}