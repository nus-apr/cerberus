/*
-------------------------------------------- 
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0. 
 - Use of C Structures is mandatory.
---------------------------------------------

You will be provided two sets, you need to print the elements in the union of the two sets.
Note that: Sets have unique elements. 

You are requested to use Data-Structures for solving this problem such that it specifies the details of a set. Such a data-structure can have two fields, one specifying the number of elements in the array, and the second a pointer to an integer array. You are supposed to dynamically allocate the space for storing the elements of the set. 

Input-Format:
First line containing the number of elements in the first set.
Second line containing the elements (space separated) of the first set.
Third line containing the number of elements of the second set.
Fourth line containing the elements (space-separated) of the second set.

Output Format: 
In a line print the elements that are present in the union of the two sets (in sorted order).

Sample Input 1
4
1 2 3 4
5 
2 3 4 5 6

Sample Output1:
1 2 3 4 5 6

Note: You may require a sorting routine to sort the elements of a set.
*/
#include <stdio.h>
#include <stdlib.h>

struct Set{
	int size;
	int * elements;
};

void inputSet(struct Set * set, int size) {
	set->size = size;
	set->elements = (int *) malloc(sizeof(int)*size);
	int i=0;
	for(i=0;i<size;i++) {
		scanf("%d",set->elements+i);
	}
}

int comp (const void * elem1, const void * elem2) 
{
    int f = *((int*)elem1);
    int s = *((int*)elem2);
    if (f > s) return  1;
    if (f < s) return -1;
    return 0;
}

void printUnion(struct Set set1,struct  Set set2) {
	int * unionArray = (int *) malloc(sizeof(int)*(set1.size+set2.size));
	int i,j,ind;
	for(i=0,ind=0;i<set1.size;i++,ind++) {unionArray[ind]=set1.elements[i];}
	for(i=0;i<set2.size;i++) {
		for(j=0;j<set1.size;j++) {
			if(set2.elements[i]==set1.elements[j]) break;
		}
		if(j==set1.size) unionArray[ind++]=set2.elements[i];
	}
	qsort(unionArray,ind,sizeof(int),comp);
	for(i=0;i<ind;i++) {
		printf("%d ",unionArray[i]);
	}
	printf("\n");
}

int main() {
	int size;
	struct Set set1,set2;
	scanf("%d",&size);
	inputSet(&set1,size);
	scanf("%d",&size);
	inputSet(&set2,size);
	printUnion(set1,set2);
	return 0;
}