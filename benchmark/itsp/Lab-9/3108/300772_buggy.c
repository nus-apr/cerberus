/*numPass=4, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
7 3 8 2 6", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
7 3 8 1 6", ExpOutput:"NO
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10
1 2 3 4 5 6 7 8 9 10", ExpOutput:"NO
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"20
5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 95", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"20
100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 134", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 80", ExpOutput:"NO
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 99", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>

int n, array[20]; // n won't be more than 20



int main()
{   int i,j,add=0;
	scanf("%d",&n);// read n;
	
	for (i=0;i<n;i++)
	{ scanf("%d", &array[i]);}// read n elements into array
	
	for (j=0;j<n;j++)
	{ add=add+array[i];}
	
    if (add%2==0)
    printf("YES");
    else
    printf("NO");
    
	
  

}