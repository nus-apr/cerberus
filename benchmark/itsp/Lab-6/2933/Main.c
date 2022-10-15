/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly 
- Function use and modular programming
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Given two integer arrays (let's say A1 and A2), check if A2 is a contiguous subarray of A1. A2 is a contiguous subarray if all elements of A2 are also present in A1 in the same order and continuously.

For ex. [12,42,67] is a contiguous subarray of [1,62,12,42,67,96]
Whereas, [1,23,21] and [12,42,96] are not contiguous subarrays of [1,62,12,42,67,96]

Input Specification: 
The first line contains the size N1 of first array.
Next line contains N1 space separated integers giving the contents of first array.
Next line contains the size N2 of second array.
Next line contains N2 space separated integers giving the contents of second array.

Output Format:
Output must be either YES or NO (followed by a new line).

Variable Constraints:
The array sizes are smaller than 20.
Each array entry is an integer which fits an int data type.

Example:
Input:
4
34 13 42 14
2
13 42
Output:
YES

Input
3
1 2 18
2
2 12
Output:
NO
*/
#include <stdio.h>
#define MAX 20

int main(){
	int A1[MAX], n1, A2[MAX], n2;
	int i, j, present;
	// Read array 1
	scanf("%d",&n1);
	for(i=0; i<n1; i++){
		scanf("%d",&A1[i]);
	}
	// Read array 2
	scanf("%d",&n2);
	for(i=0; i<n2; i++){
		scanf("%d",&A2[i]);
	}
	for(i=0; i<n1-n2; i++){
		present=1;
		for(j=0; j<n2; j++){
			if(A1[i+j] != A2[j]){
				present=0;
			}
		}
		if (present==1){
			printf("YES\n");
			return 0;
		}
	}
	printf("NO\n");
	return 0;
}