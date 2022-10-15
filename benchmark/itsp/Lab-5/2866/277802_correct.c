/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"89", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:1, Input:"59", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"Yes"
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

int check_prime(int num)//defining the fuction
{
  int i=2,div;//declaring the variable
  //div=num%i;
while(i<=(num/2))//loop)
{
  div=num%i;

     if(div==0)//condition
        return 0 ;
     else
        i=i+1;//incrementation
}
return 1;
}


int main()//main function
{
    int n,check1,check2,x=2,y=0;//declaring the variable
    scanf("%d",&n);
    
    
    while(x<=n-2)//loop
    {
        check1=check_prime(x);
        check2=check_prime(n-x);
    if(check1==1&&check2==1){
    y=1;
    printf("Yes");
        break;
    }
    x=x+1;
    }
    if(y==0)//condition
    printf("No");
    
    
	
	
	return 0;
}