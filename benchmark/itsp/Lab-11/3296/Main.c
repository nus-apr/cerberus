/*
--------------------------------------------
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0 marks. 
---------------------------------------------

Given a set of n characters and a positive integer k, print all possible strings of length k.

Note : All the strings starting with 'a' should be printed before the strings starting with 'b' and so on. (I.e. follow the lexicographic ordering.)

Example :

Input (the first number is n followed by n characters and k respectively):
2
a 
b
3

Output:
aaa
aab
aba
abb
baa
bab
bba
bbb
*/
#include <stdio.h>
int n;
int k;


void disp(char result[],int len){
	for(int i=0;i<len;i++)
			printf("%c",result[i]);
		printf("\n");
}

void printLengthK(char set1[],int len,char result[]){
	if(len==k){
		disp(result,len);
		return;
	}

	for(int i=0;i<n;i++){
		result[len] = set1[i];
		printLengthK(set1,len+1,result);
	}
		
}
int main(){

	scanf("%d\n",&n);
	char set1[n];
	for(int i=0;i<n;i++){
		scanf("%c\n",&set1[i]);
	}
	scanf("%d",&k);	
	
	char result[k];
	printLengthK(set1,0,result);
 	return 0;
}