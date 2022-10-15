/*numPass=4, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
7 3 8 2 6", ExpOutput:"YES
", Output:"YES
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
7 3 8 1 6", ExpOutput:"NO
", Output:"YES
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10
1 2 3 4 5 6 7 8 9 10", ExpOutput:"NO
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"20
5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 95", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"20
100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 134", ExpOutput:"YES
", Output:"YES
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 80", ExpOutput:"NO
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 99", ExpOutput:"YES
", Output:"YES
"
*/
#include <stdio.h>

int n, array[20],sum=0; // n won't be more than 20

int areSplitsEqual(int len, int sum_split_A, int sum_split_B)
{
    if(len>=n||sum_split_A==sum||sum_split_B==sum) //base case
    return 0;
    if (sum_split_A==(sum/2)) return 1;
    sum_split_A+=array[len];
    if (sum_split_A==(sum/2)) return 1;
    else
    return areSplitsEqual(len+1,sum_split_A,sum_split_B)||areSplitsEqual(len+1,sum_split_A-array[len],sum_split_B+array[len]);
    //recursive call
    
    
    
}

int main()
{
    int i;
	scanf("%d",&n);//inputs value of n
	for(i=0;i<n;i++)//inputs all no.s of array
	{
	    scanf("%d",&array[i]);
	}
	for(i=0;i<n;i++)//finds sum of all no.s in array
	{
	    sum=sum+array[i];
	}
	printf("%s\n", areSplitsEqual(0, 0, 0)==1?"YES":"NO");
}