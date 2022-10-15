/*
--------------------------------------------
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
TAs: Recursive algorithm is required.
 ---------------------------------------------

Given a positive number n, you need to give as an output the following pattern. You need to use recursion. No marks if loops are used.

Example 1
Input:
11

Output:
11 6 1 -4 1 6 11

Example 2
Input:
15

Output
15 10 5 0 5 10 15
*/
#include <stdio.h>

void pattern(n){
	if(n<=0){
		printf("%d ",n);
		return;
	}	
	else{
		printf("%d ",n);
		pattern(n-5);
		printf("%d ",n);
	}
}

int main(){
	int n;
	scanf("%d",&n);
	pattern(n);
	return 0;
}

