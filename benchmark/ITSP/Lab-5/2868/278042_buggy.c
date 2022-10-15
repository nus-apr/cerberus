/*numPass=4, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"18", ExpOutput:"3
", Output:"4"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"0
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:1, Input:"24", ExpOutput:"4
", Output:"5"
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
    int i,p=0,j=0;
    for(i=2;i<num;i++)
    {
        if(num%i==0)
        {
            break;
        }
        else
        {
            p=p+1;
        }
    }
    if(p==num-2)
    {
        j=1;
    } 
    return j;
}


int main(){
    int a,b,i,j,k=0;
    scanf("%d",&a);
    for(b=2;b<a;b++)
    {
        i=check_prime(b);
        if(b+2<a)
        {
            j=check_prime(b+2);
        }
        if(i==1&&j==1)
        {
            k=k+1;
        }
        
    }
    printf("%d",k);
    return 0;
}