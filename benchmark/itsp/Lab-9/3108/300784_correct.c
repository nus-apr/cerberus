/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
7 3 8 2 6", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"5
7 3 8 1 6", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"10
1 2 3 4 5 6 7 8 9 10", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"20
5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 95", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"20
100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 134", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 80", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 99", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>

int n, array[20]; // n won't be more than 20

int function(int sum, int sum_without,int n)
{
    if(sum ==n)
    {
        return 1;
    }
    for(int i=0;i<n;i++)
    {
        if(function(sum,sum,n) || function(sum+array[i],sum,n))
        {
            return 1;
        }
    }
    
}



int main()
{int sum=0;
	scanf("%d",&n);
	for(int i=0;i<n;i++)
	{
	    scanf("%d",&array[i]);
	}
	for(int i=0;i<n;i++)
	{
	   sum+= array[i]; 
	}
	
 if(sum%2 ==1)
 {
     printf("NO");
 }
 if(sum%2 ==0)
 {
   if(function(0,0,sum/2))
   {
       printf("YES");
   }
 }
 
}