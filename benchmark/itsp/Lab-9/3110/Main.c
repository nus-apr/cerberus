/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.

- You have to solve this problem using recursion 
- Some marks are reserved for writing correct base case and recursive step  
-------------------------------------------------------------------------------------------

Write a recursive function that will print all the permutations of the characters of a given string. All the permutations should be separated by a newline in the output. We will test your code manually, so you can print the permutations in any order. (Do not worry if ITS is rejecting your solution due to order differences.)

Input: abc
Output: 
abc 
acb 
bac 
bca 
cab 
cba

Input: qw
Output: 
qw 
wq

Input: r
Output: r
*/
#include <stdio.h>
#include <string.h>

void swap(char *x, char *y)
{
    char temp;
    temp = *x;
    *x = *y;
    *y = temp;
}

void permute(char *a, int l, int r)
{
   int i;
   if (l == r)
     printf("%s\n", a);
   else
   {
       for (i = l; i <= r; i++)
       {
          swap((a+l), (a+i));
          permute(a, l+1, r);
          swap((a+l), (a+i)); //backtrack
       }
   }
}
 
/* Driver program to test above functions */
int main()
{
    char str[10];
    scanf("%s", str);
    int n = strlen(str);
    permute(str, 0, n-1);
    return 0;
}
