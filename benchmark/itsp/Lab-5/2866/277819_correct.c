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

int check_prime(int num)
{
      int j,i;
      i=2;
      if(num==2)
      return 1;
      while (i<num) //loop will only operate till i<num
      {
       j=num%i;
       if(j == 0)
       return 0;    //if j is composite return the value to 0
       i=i+1;
      }
      return 1;
      
}

int main(){
	int num,i;
	scanf("%d",&num);
	int chk1,chk2;
	for(i=2;i<=(num-2);i++)
	{
	    chk1=check_prime(i);           //checking if the number is prime
	   chk2=check_prime(num-i);
	   if((chk1==1)&&(chk2==1))
	   break;
	}
	 if((chk1==1)&&(chk2==1))
    {	          
         printf("Yes");   //print yes if number is prime
    }
	else
    {
         printf("No");    //print no if number is composite
    } 
	 return 0;
}