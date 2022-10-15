/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.

- You have to solve this problem using recursion 
- Some marks are reserved for writing correct base case and recursive step  
-------------------------------------------------------------------------------------------

Write a C program, using recursion, to check if the given string is a palindrome or not. A palindrome is a word, phrase or sentence that reads the same backward or forward. The string would only contain lower case letters.

Input: liril
Output: Yes

Input: oolaleloo
Output: No
*/
#include <stdio.h>
#include <string.h>
 
void check(char [], int);
 
int main()
{
    char word[20];
    scanf("%s", word);
    check(word, 0);
    return 0;
}
 
void check(char word[], int index)
{
    int len = strlen(word) - (index + 1);
    if (word[index] == word[len])
    {
        if (index + 1 == len || index == len)
        {
            printf("Yes\n");
            return;
        }
        check(word, index + 1);
    }
    else
    {
        printf("No\n");
    }
}