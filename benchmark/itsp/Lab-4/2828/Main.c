/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments for non trivial code 
- Indentation: align your code properly 
- Use of character constants instead of ASCII values ('a', 'b, ..., 'A', 'B', ..., '0', '1' etc instead of ASCII values like 65, 66, 48 etc.)
-----------------------------------------------------------------------------------------------------------------------------------------------------------------

Write a C program to determine whether an input character is a capital letter, a small-case letter, or a digit. Do not use any library function, like isupper(), islower(), otherwise no marks will be awarded. 

Example: 
Input: 
A 
Output: 
Capital Letter 

Input: 
5 
Output: 
Digit 

Input: 
c 
Output: 
Small Letter
*/
#include<stdio.h>

int main()
{
    char c;
    scanf("%c", &c);
    if('a' <= c && c <= 'z')
        printf("Small Letter");
    else if('A' <= c && c <= 'Z')
        printf("Capital Letter");
    else if('0' <= c && c <= '9')
        printf("Digit");
    return 0;
}