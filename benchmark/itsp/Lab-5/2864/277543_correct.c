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
 int i,c=0;
 for(i=1;i<=num;i++)
 {
     if(num%i==0)
     {
       c++;
     }
 }
 if(c==2)
 {
     return(num);
 }
 else
 {
 return(0);
 }
}

int main(){
	int n1,n2,p,i;
	scanf("%d%d",&n1,&n2);
	for(i=n1;i<=n2;i++)
	{
	    p=check_prime(i);
	    if(p==i)
	    printf("%d ",p);
	}
	return 0;
}