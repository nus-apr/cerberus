/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly 
- Function use and modular programming
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Given an integer array, detect if it contains duplicate elements.

Input Specification: 
First line contains size N of the array.
Next line contains N space separated integers giving the contents of the array.

Output Format:
Output YES or NO (followed by a newline).

Variable Constraints:
The array size is smaller than 50.
Each array entry is an integer which fits an int data type.

Example:
Input:
4
34 13 42 13

Output:
YES

Input
4
11 2 18 22

Output:
NO

*/
#include <stdio.h>
#define MAX 50

int main(){
	int A[MAX], n;
	int i, j;
	int duplicate=0;
	scanf("%d",&n);
	for(i=0; i<n; i++){
		scanf("%d", &A[i]);
	}
	for(i=0; i<n; i++){
		for(j=0; j<i; j++){
			if (A[i] == A[j]){
				duplicate = 1;
			}
		}
	}
	if (duplicate == 1){
		printf("YES\n");
	}else{
		printf("NO\n");
	}
	return 0;
}