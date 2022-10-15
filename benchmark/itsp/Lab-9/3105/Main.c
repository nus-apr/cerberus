/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.

- You have to solve this problem using recursion 
- Some marks are reserved for writing correct base case and recursive step  
-------------------------------------------------------------------------------------------

Write a recursive C function to reverse a given string and then print it. The input consists of 2 lines: First line gives the length of the string; Second lines gives the string. The length of the string would not exceed 100 characters.

For Example:
Input:
6 
Hello
Output: 
olleH

Input: 
14
baL noisruceR
Output: 
Recursion Lab
*/
#include <stdio.h>
#include <string.h>
 
void reverse(char [], int, int);
int main()
{
    char str[100];
    int size, i;
    scanf("%d", &size);
    for (i=0; i<size; i++)
        scanf("%c", &str[i]);
    str[size] = '\0';    
    reverse(str, 0, size-1);
    printf("%s\n", str);
    return 0;
}
 
void reverse(char str1[], int index, int size)
{
    char temp;
    temp = str1[index];
    str1[index] = str1[size - index];
    str1[size - index] = temp;
    if (index == size / 2)
    {
        return;
    }
    reverse(str1, index + 1, size);
}