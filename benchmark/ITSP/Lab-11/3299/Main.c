/*
-------------------------------------------- 
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for non-trivial code 
- Indentation: align your code properly 
- Function use and modular programming 
- Do not include anything in the header other than what is already given in the template. 
- You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0 
- TAs: Please ensure that the submission is doing quick sort and not any other sorting routine. ---------------------------------------------

Quicksort (in ascending order) is a divide and conquer algorithm. Quicksort first divides a large array into two smaller sub-arrays: the low elements and the high elements. Quicksort can then recursively sort the sub-arrays.

The steps are:

1. Pick an element, called a pivot, from the array.

2. Reorder the array so that all elements with values less than the pivot come before the pivot, while all elements with values greater than the pivot come after it (equal values can go either way). After this partitioning, the pivot is in its final position. This is called the partition operation.

3. Recursively apply the above steps to the sub-array of elements with smaller values and separately to the sub-array of elements with greater values.

Note: The base case of the recursion is arrays of size zero or one, which never need to be sorted. A quicksort that sorts a subarray, lo through hi (inclusive), of an array A can be expressed as function quicksort(A, lo, hi). Sorting the entire array is accomplished by calling quicksort(A, 1, length(A)).

The algorithm is described using the pseudocode below:
quicksort(A, lo, hi)
  #handle base case
  #partition the array and call quicksort recursively on the two partitions

partition(A, lo, hi)
     #select a pivot element (in this exercise, you can use the first element of the array)
     #start counters from right and left of the array
      while True //no terminating condition here
        do
            right--
        while element at the right position is greater than the pivot element
        do
           left++
        while element at the left position is less than the pivot element
        if /*insert some condition here*/
            swap A[right] with A[left]
        else 
            return right 
             #come to this case if right is the position of the pivot element after completing the partition, this is the terminating condition

Input: A positive integer n followed by a line containing n positive integers separated by space.

Output: Space separated sorted list of integers
*/
#include<stdio.h>
#include<stdlib.h>


int Partition(int* arr,int lo,int hi){
	int pivot = arr[lo];
    int i = lo;
    int j = hi;
    while(1){
    	while(arr[j]>pivot){
    		j--;
    	}
    	while(arr[i]<pivot){
    		i++;
    	}
    	if(i<j){
    		int temp = arr[i];
    		arr[i]=arr[j];
    		arr[j]=temp;
    		i++;
    		j--;
    	}
    	else{
    		return j;
    	}
    }
}

void QuickSort(int* arr,int lo, int hi){
	if(lo < hi){
		int p = Partition(arr,lo,hi);
		QuickSort(arr,lo,p);
		QuickSort(arr,p+1,hi);
	}
	return;
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

	QuickSort(arr,0,n-1);
	
	for(i=0;i<n;i++){
		printf("%d ",arr[i]);
	}
	printf("\n");
	return 0;
}