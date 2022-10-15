/*numPass=7, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"89", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"YesNo"
Verdict:ACCEPTED, Visibility:1, Input:"59", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"YesNo"
Verdict:ACCEPTED, Visibility:0, Input:"109", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:0, Input:"131", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"123", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"125", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"141", ExpOutput:"Yes
", Output:"Yes"
*/
#include<stdio.h>
int check_prime(int n)
{
    int i=2,j=0;
    while(i<n)
    {
        if(n%i==0)
            j=j+1;
        i=i+1; 
    }
    if(j>0)
        return 0;
    else
        return 1;    
}

int main()
{
    int p,i=2,flag=0;
    scanf("%d", &p);
    for(i;i<p;i++)
    {
        if((check_prime(i)==1)&&(check_prime(p-i)==1))
        {
            printf("Yes");
            break;
        }
        
        flag =flag+1;
    }   
        
    if(flag>0)
        printf("No");
    
	return 0;
}