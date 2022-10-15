/*numPass=7, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"89", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"59", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"No"
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

int check_prime(int a)
{
    for(int n=2;n<a;n++)
    {
        if(a%n == 0)
            return 0;
    }            
    return 1;
    
}
int main(){
	int N,b;
	scanf("%d",&N);
	
	
	
	for(b=2;b<N;b++)
	{
	    if ( (check_prime(b)==1) && (check_prime(N-b)==1))
	        
	
	    printf("Yes");
	
	else
	{
	    printf("No");
	}
	return 0;}
}