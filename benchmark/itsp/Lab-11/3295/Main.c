/*
--------------------------------------------
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0 
 - TAs: Please ensure that the submission is doing Comb Sort and not any other sorting routine.
---------------------------------------------

This question introduces you to new algorithms to sort n positive integers (in a non-decreasing order). 

In bubble sort, when any two elements are compared, they always have a gap (distance from each other in the array) of 1. The basic idea of comb sort is that the gap can be much more than 1.

The basic idea is to eliminate turtles, or small values near the end of the list, since in a bubble sort these slow down the sorting tremendously. Rabbits, large values around the beginning of the list, do not pose a problem in bubble sort.

In other words, the inner loop, which does the actual swap, is modified such that the gap between swapped elements goes down (for each iteration of outer loop) in steps of shrink factor. i.e. [ n/shrink , n/shrink^2, n/shrink^3, ...., 1 ]. Unlike in bubble sort, where the gap is constant i.e. 1.

The gap starts out as the length of the list being sorted divided by the shrink factor (generally 1.3; see below), and the list is sorted with that value (rounded down to an integer if needed) as the gap. Then the gap is divided by the shrink factor again, the list is sorted with this new gap, and the process repeats until the gap is 1. At this point, comb sort continues using a gap of 1 until the list is fully sorted. The final stage of the sort is thus equivalent to a bubble sort, but by this time most turtles have been dealt with, so a bubble sort will be efficient.

The algorithm is described in the following pseudocode:

1. Choose the gap = n/shrink.

2a. If the gap is *strictly greater* than 1, do a single pass on the list, such that in the pass, you compare the i-th element with (i+gap)-th element and swapping these elements if arr[i] > arr[i+gap]. You do this for all i, from i=0, till i+gap>=n.

2b. If the gap is equal to 1, do a pass (of swaps, the same as in 2a) over the whole list and since gap==1,  i+gap is the same as i+1, i.e. you compare the adjacent elements throughout the pass. If there are no swaps in this pass, exit and return the now sorted list.

3. Decrease the gap by dividing it by the shrink factor and do step 2 again. If the gap is less than 1, set gap equal to 1 and do step 2 again.

(Please note that when gap==1, you are essentially doing a bubble sort on the whole list! Hence the list is bound to be sorted at the end of this subroutine. However, the wonderful thing about this sorting algorithm is that it is much faster than bubble sort, in general!)

Note: Use a shrink factor of 1.3 for this assignment.

Input: A positive integer n followed by a line containing n positive integers separated by space.
 
Output: Space separated sorted list of integers.
*/
#include<stdio.h>
#include<stdlib.h>

void CombSort(int* arr, int n){
    int gap = n;
   	float shrink = 1.3;
   	
   	int swapped = 1;
    while(gap>=1 && swapped==1){
        gap = (int) ((float)gap)/shrink;
        if(gap<1)	gap=1;
        
        
        int i=0;
        if(gap==1)
        	swapped=0;

        while((i+gap)<n){
        	if(arr[i]>arr[i+gap]){
        		int temp = arr[i];
        		arr[i]=arr[i+gap];
        		arr[i+gap]=temp;
        		if(gap==1)
        			swapped=1;
        	}
        	i++;
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

	CombSort(arr,n);
	
	for(i=0;i<n;i++){
		printf("%d ",arr[i]);
	}
	printf("\n");
	return 0;
}