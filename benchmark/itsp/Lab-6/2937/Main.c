/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly 
- Function use and modular programming
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Given two arrays sorted in non descending order, merge them in a single non descending array.

Input Specification: 
First line contains size N1 of first array.
Next line contains N1 space separated integers giving the contents of first array.
Next line contains size N2 of second array.
Next line contains N2 space separated integers giving the contents of second array.

Output Format:
Output the elements of merged array (each followed by a newline).

Variable Constraints:
The array size is smaller than 20.
Each array entry is an integer which fits an int data type.

Example:
Input:
5
1 2 5 9 16
3
3 5 21

Output:
1
2
3
5
5
9
16
21

Input
2
1 2
3
12 31 45

Output:
1
2
12
31
45

*/
#include <stdio.h>
#define MAX 20

int main(){
	int N1, N2;
	int A1[MAX], A2[MAX], ANS[2*MAX];
	int A1_index=0, A2_index=0, index_sum=0;
	int i;
	// Read array 1
	scanf("%d",&N1);
	for(i=0; i<N1; i++){
		scanf("%d",&A1[i]);
	}
	// Read array 2
	scanf("%d",&N2);
	for(i=0; i<N2; i++){
		scanf("%d",&A2[i]);
	}
	while(index_sum<N1+N2){
		if (A1_index>=N1){					// Array A1 is completely merged
			ANS[index_sum] = A2[A2_index];
			A2_index++;
			index_sum++;
		}else if (A2_index>=N2){		    // Array A2 is completely merged
			ANS[index_sum] = A1[A1_index];
			A1_index++;
			index_sum++;
		}else{
			if (A1[A1_index] < A2[A2_index]){	// A1 contains smaller element
				ANS[index_sum] = A1[A1_index];
				A1_index++;
				index_sum++;
			}else{						// A2 contains smaller element
				ANS[index_sum] = A2[A2_index];
				A2_index++;
				index_sum++;
			}
		}
	}
	for(i=0; i<N1+N2; i++){
		printf("%d\n", ANS[i]);
	}
	return 0;
}