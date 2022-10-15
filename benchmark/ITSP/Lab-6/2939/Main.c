/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly
- Function use and modular programming
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Given an integer array, print the length of longest ascending (strictly increasing) subsequence.

For example, for array A = [1, -2, 3, -5, 5], the longest ascending subsequence is [1, 3, 5]. Hence, the output is:
3

Hint:
Let A[0..n-1] be the input array. Let's create another array MaxTill[0..n-1]. In this array, MaxTill[i] denotes the length of longest ascending subsequence till index i such that A[i] is an element of the longest sequence.
So, MaxTill[i] can be written as
MaxTill[i] = max(
     max( 1+MaxTill(j) )     where j < i and A[j] < A[i]
     1                                 if there is no such j
)

The length of longest ascending subsequence will be the max of all values in MaxTill[0..n-1]

Input Specification: 
First line contains size N of the array.
Next line contains N space separated integers giving the contents of the array.

Output Format:
Output the length of longest ascending subsequence.

Variable Constraints:
The array size is smaller than 20.
Each array entry is an integer which fits an int data type.

Example:
Input:
5
1 -2 3 -5 5

Output:
3
*/
#include <stdio.h>
#define MAX 20

int max(int a, int b){
	return a>b?a:b;
}

int main(){
	int n, i, j, max_val, ans=0;
	int A[MAX], MAXVAL[MAX];
	scanf("%d", &n);
	for(i=0; i<n; i++){
		scanf("%d",&A[i]);
	}
	MAXVAL[0] = 1;
	for(i=1; i<n; i++){
		max_val=1;
		for(j=0; j<i; j++){
			if(A[j]<A[i]){
				max_val = max(MAXVAL[j]+1, max_val);
			}
		}
		MAXVAL[i] = max_val;
	}
	for(i=0; i<n; i++){
		ans = max(ans, MAXVAL[i]);
	}
	printf("%d\n", ans);
	return 0;
}