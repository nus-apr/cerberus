/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>

int check_prime(int num)
{   int k; 
    for(k=2;k<=sqrt(num);k++)
    {
        if(num%k==0)
        {
            return 0;
        }
    }
    return 1;
}

int main(){
    
    int n1,n2,a;
    
    scanf("%d %d",&n1,&n2);
    
    for(a=n1;a<=n2&&a>=n1&&a>1;a++)
    {
        if(check_prime(a)==1)
        {
            printf("%d ",a);
        }
    }
    
	return 0;
}