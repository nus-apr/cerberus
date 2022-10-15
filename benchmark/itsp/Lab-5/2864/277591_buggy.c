/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"3 5 7 11 13 17 19 "
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>
#include<math.h>
int check_prime(int num)
{
    if(num%2==0||num==1)
    return 0;
    int j,k;
    k=sqrt(num);
    for(j=3;j<=k;j++)
    {
     if(num%j==0)
     return 0;
    }
    return 1;
}
void disp_prime(int a)
{
    printf("%d ",a);
}
void process(int n1,int n2)
{
   int i,c;
   for(i=n1;i<=n2;i++)
   {
       c=check_prime(i);
       
       if(c!=0)
       disp_prime(i);
   }
}
void ent_num()
{
    int n1,n2;
    scanf("%d%d",&n1,&n2);
    process(n1,n2);
}

int main(){
	ent_num();
	return 0;
}