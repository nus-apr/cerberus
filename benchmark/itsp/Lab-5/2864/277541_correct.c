/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:ACCEPTED, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"2 3 5 7 11 13 17 19 "
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>

int check_prime(int num)
{
    int i,c;
    if(num==1)
        return 0;
    else
    {
        c=1;
        for(i=2;i<=num/2;i++)
        {
            if(num%i==0)
                c=c+1;
        }
    }
        if(c==1)
            return num;
    else
        return 0;
}


int main()
{
    int n1,n2,i;
    scanf("%d %d",&n1,&n2);
    for(i=n1;i<=n2;i++)
    {
        if(check_prime(i)!=0)
            printf("%d ",check_prime(i));
    }
    
    	return 0;
}
