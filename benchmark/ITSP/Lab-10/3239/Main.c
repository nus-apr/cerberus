/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.
 - Use pointers only and when required allocate memory Dynamically instead of static memory allocation otherwise you will get 0 marks.
-----------------------------------------------------------------------------------------------------------------------------------------------------
You are given two strings as input. Write a program to find out whether the two given strings are valid or not. Two strings are said to be valid if every character of one string is also present in other string at any place. Example : "abc" and "cab" are valid strings.

Note : Input character will be lower case alphabates only. Size of string will be given by the user and use dynamic memory allocation.
 
Input Format: First line contain the size of first string followed by next line containing the string itself. Similarly next line contain the size of second string followed by next line containing the string itself.

Output : Valid, if two strings are valid otherwise print Not Valid.  

Example
Input :
3
abc
3
cab

Output:
Valid
*/
#include <stdio.h>
#include <stdlib.h>

int valid(char * s1, char * s2, int n){
    int a[26] = {0}, b[26] = {0};
    for(int i = 0; i < n; i++){
        a[s1[i] - 'a'] += 1;
        b[s2[i] - 'a'] += 1;
    }
    for(int i = 0; i < 26; i++)
        if(a[i] != b[i])
            return 0;
    return 1;        
}

int main()
{
	int n1, n2;
	char *s, *t;

	scanf("%d" , &n1);
	s = (char *)malloc((n1 + 1) * sizeof(char));
	scanf("%s",s);

	scanf("%d" , &n2);
	t = (char *)malloc((n2 + 1) * sizeof(char));
	scanf("%s",t);


	if(n1 != n2)
	    printf("Not Valid");
	else if(valid(s, t, n1))
	    printf("Valid");
	else
	    printf("Not Valid");


	return 0;

}