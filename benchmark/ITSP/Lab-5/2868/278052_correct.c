/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"18", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"0
", Output:"0"
Verdict:ACCEPTED, Visibility:1, Input:"24", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"40", ExpOutput:"5
", Output:"5"
Verdict:ACCEPTED, Visibility:0, Input:"100", ExpOutput:"8
", Output:"8"
Verdict:ACCEPTED, Visibility:0, Input:"70", ExpOutput:"7
", Output:"7"
*/
#include<stdio.h>
int check_prime(int num)
{
    int k=0;
    for(int l=1;l<=num;l++)
    {
        if ((num%l)==0)
        k++;
    }
    if(k==2)
{
  return 1;
}
else
{
return 0;
}
    
}

int main()
{
    int n,x,y,i;
    int j=0;
    scanf("%d",&n);
    for(i=2;i<=n;i++)
    {
    x=check_prime(i);
    y=check_prime(i+2);
    if((x==1)&&(y==1)&&((i+2)<=n))
    {
        j++;
    }
    }
    printf("%d",j);

   return 0;
}