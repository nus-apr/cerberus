/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for non-trivial code. 
- Indentation: align your code properly. 
- Function use and modular programming. 
- Do not include anything in the header other than what is already given in the template. 
- Use pointers only and when required allocate memory Dynamically instead of static memory allocation otherwise you will get 0 marks.
------------------------------------------------------------------------------------------------------------------------------------------------
You are given two strings, find out minimum number of character deletions required to make two strings equal. You can delete any character from any string. Two strings are said to equal if every character of one string is also present in other string at any place. Example : "abc" and "cab" are equal strings.

Note : String contains lower case alphabets only. Size of string will be given by the user and use dynamic memory allocation.

Input Format : First two lines contain the size of the first string and the string itself. Next two lines contain the size of the second string and the string itself.

Output Format : Print minimum number of character deletions required to make the strings equal.

Example:
Input :
3 
cde
3
abc

Output:
4 
*/
#include <stdio.h>
#include <stdlib.h>
int makeEqual(char * s1, int n1, char * s2, int n2){
    int a[26] = {0}, b[26] = {0}, i, r = 0;
    for(i = 0; i < n1; i++)
        *(a + *(s1 + i) - 'a') += 1;
    for(i = 0; i < n2; i++)
        *(b + *(s2 + i) - 'a') += 1;
    for(i = 0; i < 26; i++)
        r = r + abs(*(a + i) - *(b + i));
    return r;    
}
int main(){
    int n1, n2;
    char *s1, *s2;
    scanf("%d\n", &n1);
    s1 = (char *)malloc(n1 * sizeof(char));
    for(int i = 0; i < n1; i++)
        scanf("%c", (s1 + i));
    scanf("\n%d\n", &n2);
    s2 = (char *)malloc(n2 * sizeof(char));
    for(int i = 0; i < n2; i++)
        scanf("%c", (s2 + i));
    printf("%d", makeEqual(s1, n1, s2, n2));
    return 0;
}