/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.

- You have to solve this problem using recursion 
- Some marks are reserved for writing correct base case and recursive step  
-------------------------------------------------------------------------------------------

Given an array of $N$ ints, is it possible to choose a group of some of the ints, such that the group sums to the given target $T$? 
Input will consist of two lines : space separated integers $N$ and $T$ in first line followed by $N$ space separated integer elements ($a_1 ... a_N$ ) of array in second line.
Output should be single line - either "YES" or "NO".

Assume :  $T, a_i$ and $\Sigma a_i$ can be accommodated in int data type. Also $N \leq 30$

Input :
4 2
3 5 7 1
Output :
NO

Input :
4 10
3 5 7 2
Output :
YES
*/
#include <stdio.h>

int N, T, array[30];

int groupSum(int len_covered, int partial_sum)
{
	if(len_covered == N)
		return partial_sum == T;
	else if(partial_sum == T)
	    return 1;
	else
		return ( groupSum(len_covered+1, partial_sum+array[len_covered]) || groupSum(len_covered+1, partial_sum) );
}

int main()
{
	int i;
	scanf("%d%d", &N, &T);
	for(i=0; i<N; i++)
		scanf("%d", &array[i]);

	printf("%s\n", groupSum(0, 0)==1?"YES":"NO");
}
