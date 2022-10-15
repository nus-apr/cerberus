/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3571113171923"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5711131719232931"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"235711131719"
Verdict:WRONG_ANSWER, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"2329313741434753"
Verdict:WRONG_ANSWER, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"3137414347"
*/
#include<stdio.h>

int check_prime(int num)
{
    int i;
    for (i=2; i<num; i++)
    {
        if(num%i==0)
        return 0;
    }
     return 1;
}

//Complete the function definitions here.

int main()
{
    int n1,n2,j;
        scanf("%d %d", &n1, &n2);
        if(n1==1)
            n1++;
    for (j=n1; j<=n2; j=j+1)
    {
        if(check_prime(j)==1)
        printf("%d", j);
      
    }
    
    
    
    
    
    
    

	
	
	
	return 0;
}