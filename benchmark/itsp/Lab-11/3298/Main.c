/*
--------------------------------------------
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0 
 - TAs: Please ensure that the submission is using the recursive idea behind Merge Sort.
---------------------------------------------
Counting Inversions

An inversion in a list of elements a1, a2, ... , an is a pair of elements {ai,aj} such that ai > aj and i < j. To count the total number of inversions in a list of elements, you can modify the standard MergeSort algorithm. Essentially, in the recursive definition of MergeSort, count the number of inversions in each half and count the number of *cross-inversions*, i.e. {ai, aj} such that ai>aj and ai lies in the first half and aj lies in the second half.

Please note that you have to keep the sorting routine of MergeSort *as-it-is* and add some additional processing steps to count the number of inversions.

In this question, implement the algorithm to count the number of inversions and print the sorted list. The algorithm is described using the pseudocode below:
sort-and-count(L)
  #handle base case for list L
     #divide L into A, B   (almost equal parts)
     #*recursively* count rA and rB, which are the number of inversions in A and B respectively
     #get r which is the number of cross-inversions and get a merged list L from the merging routine using the sorted lists A and B
     #return rL = rA+rB+r, L

merge-and-count(A,B)
  #standard merge routine from merge sort
  #increase count of "cross-inversions" in A and B by x, when an element from B is pushed to the return list before x remaining elements of A 
  #return count and (merged list from A and B)

Input: A positive integer n followed by a line containing n positive integers separated by space.

Output: Number of inversions in the list followed by the sorted list (elements separated by space) in the next line.
*/
#include<stdio.h>
#include<stdlib.h>

int MergeAndCount(int* arr, int lo, int hi){
	
	int* temp;
	temp = (int*) malloc((hi-lo+1)*sizeof(int));

	int mid=(lo+hi)/2;
	int i=lo;
	int j=mid+1;
	int k=0;

	int count = 0;

	while(i<=mid && j<=hi){
		if(arr[i]>arr[j]){
			temp[k++]=arr[j++];
			count+= (mid-i+1);
		}
		else{
			temp[k++] = arr[i++];
		}
	}

	while(i<=mid){
		temp[k++]=arr[i++];
	}
	while(j<=hi){
		temp[k++]=arr[j++];
	}

	for(i=0;i<=(hi-lo);i++){
		arr[i+lo]=temp[i];
	}

	free(temp);
	return count;
}



int SortAndCount(int* arr, int lo, int hi){
	int mid=(hi+lo)/2;
	if(hi>lo){
		int count1 = SortAndCount(arr, lo,mid);
		int count2 = SortAndCount(arr,mid+1,hi);
		int count3 = MergeAndCount(arr,lo,hi);
		return (count1+count2+count3);
	}
	else{
		return 0;
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

	int count = SortAndCount(arr,0,n-1);
	
	printf("%d\n",count);
	for(i=0;i<n;i++){
		printf("%d ",arr[i]);
	}
	printf("\n");

	return 0;
}