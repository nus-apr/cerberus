/*numPass=4, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"18", ExpOutput:"3
", Output:"4"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"0
", Output:"1"
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

int check_prime(int num){
    int i;
    for(i=2;i<=num/2;i++)
    {
        if(num%i==0)
        {
            return 0 ;
        }
    }
    return 1;
}

//Complete function definitions

int main(){
    int j,n,c;
    int count=0;
    scanf("%d",&n);
    for(j=2;j<=n;j++)
    {
    c=check_prime(j);
    if(c==1)
    {
        c=check_prime(j+2);
        if(c==1)
        {
        count=count+1;
        }
    }
    }
    printf("%d",count);
    //Write your code here
    
    return 0;
}