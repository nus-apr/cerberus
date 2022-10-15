/*numPass=4, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"6 15
4 7 1 17 13 5", ExpOutput:"NO
", Output:"NO
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"12 42
1 1 2 2 3 3 4 4 5 5 6 6", ExpOutput:"YES
", Output:"NO
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9 42
10 10 10 10 10 2 1 1 2", ExpOutput:"YES
", Output:"NO
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 10 
3 5 7 1", ExpOutput:"YES
", Output:"NO
"
Verdict:ACCEPTED, Visibility:1, Input:"4 2
3 5 7 1", ExpOutput:"NO
", Output:"NO
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"25 83
1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15", ExpOutput:"YES
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"24 522
5 10 15 20 25 30 5 10 15 20 25 30 5 10 15 20 25 30 5 10 15 20 25 30", ExpOutput:"NO
", Output:"NO
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"15 186
40 50 60 64 52 40 50 10 30 16 18888 1200 181 286 10", ExpOutput:"YES
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"20 5455
200 200 200 400 500 600 700 800 900 1000 1 2 3 4 5 10 9 8 7 6", ExpOutput:"NO
", Output:"NO
"
*/
#include <stdio.h>

int N, T, array[30]; // N won't be larger than 30

int groupSum(int len_covered, int partial_sum)
{
    int sum=0;
    // Write appropriate base cases
    if(N==0 || len_covered==N)
    return 0;
    if(sum==T)
    return 1;
    sum=groupSum(len_covered+1,T);
    // Write required recursive calls
    return groupSum(len_covered+1,T-array[len_covered-1]);
}

int main()
{
	// (read N, T, and elements of array)
	scanf("%d %d\n",&N,&T);
	for(int i=0;i<N;i++)
	scanf("%d ",&array[i]);
	printf("%s\n", groupSum(0, 0)==1?"YES":"NO");
	return 0;
}