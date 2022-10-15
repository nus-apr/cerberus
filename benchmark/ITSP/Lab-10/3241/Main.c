/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.
 - Use pointers only and when required allocate memory Dynamically instead of static memory allocation otherwise you will get 0 marks. All Strings are to be allocated dynamically.

Amber, a freshman student at IIT Kanpur, recently learned about GCD and how to compute them for two numbers. She wanted to extend the definition of divisors and GCD to strings. Here is what she came up with :

String s1 is the divisor of string s2 if and only if there exists a positive integer x such that if we write out string s1 consecutively x times, we get string s2. For example, string "abab" has two divisors — "ab" and "abab".

Now Amber wants to calculate the Greatest common divisor of two strings. She is not that good in coding and wants your help for the same. 

INPUT :
The first input line contains a non-empty string s1.
The second input line contains a non-empty string s2.

OUTPUT :
Print the Greatest Common Divisor of s1 and s2. Return empty string if no common divisor exists. 
*/
#include <stdio.h>
#include <stdlib.h>

#define true 1
#define false 0


// a program to check if the first i characters of the string are a factor of it. 
int isfactor(char s[] , int n , int i ){
	if (n % i != 0 )
		return false; 

	if( i == 0 || i > n )
		return false; 

	if (n == 0) 
		return true; 

	for(int j = 0 ; j < n ; j++)
		if(*(s + j) != *(s + j%i))
			return false;

	return true;
}

int get_len(char s[])
{
	int i = 0 ; 
	while(*(s + i) != '\0')
		i++;

	return i ; 
}

int main(){

	int n1, n2 , i; 
	char *s, *t ; 

	scanf("%d" , &n1);
	s = (char *)malloc((n1 + 1) * sizeof(char));
	scanf("%s",s);

	scanf("%d" , &n2);
	t = (char *)malloc((n2 + 1) * sizeof(char));
	scanf("%s",t);

 	int max = -1;

	for( i = 0  ; i < get_len(s) && i < get_len(t) ; i++)
	{
		if (isfactor(s , get_len(s) , i + 1) && isfactor(t , get_len(t) , i + 1))
			max = i;
	}

	s[max + 1] = '\0';
	printf("%s", s);
	return 0 ; 

}