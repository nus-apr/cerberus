/*
--------------------------------------------
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0 marks. 
 - Use Recursion.
---------------------------------------------
Given a number x, print all the sequences whose sum is equal to x. Also, only those sequences should be printed which are non- increasing. You need to use recursion for the same.

Note: All the non-increasing sequences starting with 1 should be printed before the ones starting with 2 and so on.

Example:

Input : 
4

Output:
1 1 1 1
2 1 1
2 2
3 1
4

*/
#include <stdio.h>

void printSum(int x,int cur_sum,int result[],int len){
	if(cur_sum == x){
		for(int i=0;i<len;i++)
			printf("%d ",result[i]);
		printf("\n");
		return;
	}
	for(int i=1;i<=x;i++){
		if(i+cur_sum<=x && (len==0 || (result[len-1]>=i))){
			result[len] = i;
			printSum(x,cur_sum+i,result,len+1);
		}
	}
}

int main(){
	int x;
	scanf("%d",&x);
	int result[100];
	printSum(x,0,result,0);
	return 0;
}
