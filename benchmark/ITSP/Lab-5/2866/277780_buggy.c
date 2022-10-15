/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"89", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:1, Input:"59", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"109", ExpOutput:"Yes
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"131", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:0, Input:"123", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:0, Input:"125", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:0, Input:"141", ExpOutput:"Yes
", Output:"yes"
*/
#include<stdio.h>

int check_prime(int num)
{
    int i;
    for(i=2;i<num;i++)
    {
     if((num%i)==0)
     
         return 0;
    
    }
        return 1;
        
}

int main()
{
    int i,n,flag=0;
    scanf("%d",&n);
    for(i=2;i<n;i++)
    {
    if(check_prime(i) && check_prime(n-i) ){
    flag=1;
    printf("yes");
        break;
    }
        
    }
    if(flag==0)
    printf("no");
    
    
}