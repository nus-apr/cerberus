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

You will be provided two sets, you need to print the elements in the intersection of the two sets.
Note that: Sets have unique elements, and you will be provided elements of the set in sorted order. 
An element is in the intersection of two sets, if it is present in both the sets. 

You are requested to use Data-Structures for solving this problem such that it specifies the details of a set. Such a data-structure can have two fields, one specifying the number of elements in the array, and the second a pointer to an integer array. You are required to dynamically allocate the space for storing the elements of the set. 

Input Format:
First line containing the number of elements in the first set. 
Second line containing the elements (space separated) of the first set in sorted order.
Third line containing the number of elements of the second set.
Fourth line containing the elements (space-separated) of the second set in sorted order.

Output Format: 
In a line print the elements that are present in the intersection of the two sets (in sorted order).

Sample Input 1
4
1 2 3 4
5 
2 3 4 5 6

Sample Output 1:
2 3 4

Note: That the elements of the set are given in sorted order, so if you carefully loop through the set elements, you would not require sorting, as they will come in sorted order by themselves :) 
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

void printIntersect(struct Set set1,struct Set set2) {
	int i,j;
	for(i=0;i<set1.size;i++) {
		int el = set1.elements[i];
		for(j=0;j<set2.size;j++) {
			if(set2.elements[j]==el) {printf("%d ",el);break;}
		}
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
	printIntersect(set1,set2);
	return 0;
}