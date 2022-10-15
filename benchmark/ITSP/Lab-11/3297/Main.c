/*
--------------------------------------------
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0 
 - TAs: Please ensure that the submission is doing Insertion Sort and not any other sorting routine.
---------------------------------------------

Insertion sort (in ascending order) iterates, consuming one input element in each iteration, and growing a sorted output list. Each iteration, insertion sort removes one element from the input data, finds the location it belongs within the sorted list, and inserts it there. It repeats until no input elements remain.

Sorting is typically done in-place, by iterating up the array, growing the sorted list behind it. At each array-position, it checks the value there against the largest value in the sorted list (which happens to be next to it, in the previous array-position checked). If larger, it leaves the element in place and moves to the next. If smaller, it finds the correct position within the sorted list, shifts all the larger values up to make a space, and inserts into that correct position.

The algorithm is described using the pseudocode given below:

1. For all elements arr[i] (0 < i < n), if arr[i] less than arr[i-1] go to step 2, otherwise continue step 1 for the next i.

2. Find the element arr[j] such that j is the lowest index which satisfies arr[j] > arr[i]. (Such an index is bound to exist, since arr[i-1] > arr[i] after Step 1.) Put arr[i] at the j-th position in the list and shift every element, from the indices j+1 to i-1, by one place to the right.

Input: A positive integer n followed by a line containing n positive integers separated by space.
Output: Space separated sorted list of integers.
*/
#include<stdio.h>
#include<stdlib.h>

void InsertionSort(int* arr, int n){
    int i;
    for(i=1;i<n;i++){
        if(arr[i]>=arr[i-1])
            continue;
    	int j;
    	for(j=0;j<i;j++){
    		if(arr[j]>arr[i]){
    			int k=j;
    			int prev=arr[k];
    			arr[k]=arr[i];
    			for(k=j+1;k<=i;k++){
    				int curr=arr[k];
    				arr[k]=prev;
    				prev=curr;
    			}
    			break;
    		}
    	}
    }
}

int main(){
	int n;
	scanf("%d",&n);
	int* arr;
	arr = (int*) malloc(n*sizeof(int));
	
	int i;

	for(i=0;i<n;i++){
		scanf("%d",&arr[i]);
	}

	InsertionSort(arr,n);
	
	for(i=0;i<n;i++){
		printf("%d ",arr[i]);
	}
	printf("\n");
	return 0;
}