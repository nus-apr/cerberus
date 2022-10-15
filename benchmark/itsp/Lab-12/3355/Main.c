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

Two intervals overlap, if they have some point that is contained in both the intervals. 
You should design a Data-Structure such that it has two fields, namely the left index and the right index.  
Assume that the intervals specified will be closed intervals. You need to figure out, whether given two intervals, they overlap or not. 

Input Format:
First line containing two space separated integer numbers, specifying the first closed interval
Second line containing two space separated integer numbers, specifying the second closed interval

Output Format:
YES or NO in one line depending on the overlapping nature of the intervals

Sample Input 1:
4 10
-1 6
Sample Output 1: 
YES

Sample Input 2:
4 10
-1 3
Sample Output2:
NO
*/
#include <stdio.h>

struct Interval{
	int left;
	int right;
};

void setPoints(struct Interval * interval,int left,int right) {
	interval->left=left;
	interval->right=right;	
}

int checkIntersect(struct Interval int1, struct Interval int2) {
	if(int1.right<int2.left || int2.right<int1.left) return 0;
	return 1;
}

int main() {
	int left,right;
	struct Interval int1,int2;
	scanf("%d %d",&left,&right);
	setPoints(&int1,left,right);
	scanf("%d %d",&left,&right);
	setPoints(&int2,left,right);
	if(checkIntersect(int1,int2)) printf("YES\n");
	else printf("NO\n");
	return 0;
}