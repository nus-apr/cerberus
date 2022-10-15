/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"89", ExpOutput:"No
", Output:"NoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNo"
Verdict:WRONG_ANSWER, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"NoNoNoYesNoNoNoNoNoYesNoYesNoNoNoNoNoYesNo"
Verdict:WRONG_ANSWER, Visibility:1, Input:"59", ExpOutput:"No
", Output:"NoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNo"
Verdict:WRONG_ANSWER, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"NoYesNoYesNoNoNoNoNo"
Verdict:WRONG_ANSWER, Visibility:0, Input:"109", ExpOutput:"Yes
", Output:"YesNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNo"
Verdict:WRONG_ANSWER, Visibility:0, Input:"131", ExpOutput:"No
", Output:"NoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNo"
Verdict:WRONG_ANSWER, Visibility:0, Input:"123", ExpOutput:"No
", Output:"NoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNo"
Verdict:WRONG_ANSWER, Visibility:0, Input:"125", ExpOutput:"No
", Output:"NoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNo"
Verdict:WRONG_ANSWER, Visibility:0, Input:"141", ExpOutput:"Yes
", Output:"YesNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNoNo"
*/
#include<stdio.h>

int check_prime(int num)
{
 int c=0;
 for(int i=2;i<=num;i++)
    if(num%i==0)c++;
 if(c==1)return num;
 return 1;
}

int main()
{
    int N,j;
	scanf("%d",&N);
	for(int i=2;i<=((N-2)/2);i++)
	{
	 if((check_prime(i)!=1)&&(check_prime(N-i)!=1))	 
	    printf("Yes");
	 else printf("No");   
	}    
	return 0;
}