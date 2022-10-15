/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly 
- Function use and modular programming
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Given an integer array and an integer k, print the sum of every k consecutive elements.

For example, for array A = [1, 2, 3, 4, 5] and k = 3, the output will be:
6
9
12

Input Specification: 
First line contains size N of the array.
Next line contains N space separated integers giving the contents of the array.
Next line contains k.

Output Format:
Output the k Sums (each followed by a newline).

Variable Constraints:
The array size is smaller than 20.
Each array entry is an integer which fits an int data type.

Example:
Input:
4
34 13 42 14
2
Output:
47
55
56

Input
4
11 2 18 2
2
Output:
13
20
20

*/
#include <stdio.h>
#define MAX 20

int read_array(int arr[]){
	int i, n;
	scanf("%d", &n);
	for (i = 0; i < n; i++)
		scanf("%d", &arr[i]);
	return n;
}

int main(){
	int A[MAX], n, k;
	n = read_array(A);
	scanf("%d",&k);
	for(int i=0; i<=n-k; i++){
		int sum=0;
		for(int j=0; j<k; j++){
			sum += A[j+i];
		}
		printf("%d\n", sum);
	}
	return 0;
}