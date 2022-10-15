/*numPass=5, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
7 3 8 2 6", ExpOutput:"YES
", Output:"NO
"
Verdict:ACCEPTED, Visibility:1, Input:"5
7 3 8 1 6", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:1, Input:"10
1 2 3 4 5 6 7 8 9 10", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"20
5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 95", ExpOutput:"YES
", Output:"YES
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"20
100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 134", ExpOutput:"YES
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 80", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 99", ExpOutput:"YES
", Output:"YES
"
*/
#include <stdio.h>

int n, array[20],sum; // n won't be more than 20

int areSplitsEqual(int len, int sum_split_A, int sum_split_B)
{
    for(;len>=0;len--)
    {
        if(sum_split_A==sum_split_B)
            return 1;
        else
        {
            return areSplitsEqual(len-1,sum_split_A+array[len-1],sum_split_B-array[len-1]); 
        }
    }
    return 0;
}
void inar()
{
    for(int i=0;i<n;i++)
    {
        scanf("%d",array+i);
    }
}

int main()
{
	scanf("%d",&n);
	inar();
	for(int i=0;i<n;i++)
	{
	    sum+=array[i];
	}
	printf("%s\n", areSplitsEqual(n, 0,sum)==1?"YES":"NO");
	//printf("YES");
	//printf("NO");
}