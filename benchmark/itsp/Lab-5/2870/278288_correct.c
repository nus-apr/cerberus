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
    int i,d;
    d=1;
    for(i=2;i<=(num/2);i++)
    {
        if(num%i==0)
        {
            d=0;
            break;
        }
    }
    if(num==1)
      d=0;
    return d;
}
int main()
{
    int N,i;
    scanf("%d",&N);
    i=N;
    while(i>=N)
    {
        if(check_prime(i)==1)
          break;
        i++;  
    }
    printf("%d",i);
    return 0;
}