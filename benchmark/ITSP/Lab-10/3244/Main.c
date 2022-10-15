/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for non-trivial code. 
- Indentation: align your code properly. 
- Function use and modular programming. 
- Do not include anything in the header other than what is already given in the template. 
- Use pointers only and when required allocate memory Dynamically instead of static memory allocation otherwise you will get 0 marks.
-------------------------------------------------------------------------------------------------------------------------------------------------------------

Suppose you have a string S which has length N and is indexed from 0 to N - 1. String R is the reverse of the string S. The string S is good if the condition |S_i - S_(i - 1)| = |R_i - R_(i - 1)| is true for every i from 1 to N - 1.

Note: Given a string str, str_i denotes the ascii value of the str[i] character (0-indexed) of str. |x| denotes the absolute value of an integer x. Size of string will be given by the user and use dynamic memory allocation.

Input Format : First Line contains length of the string followed by string on the next line.
Output : Good String or Not Good String.

Example:
Input
4
acxz
Output
Good String

Input
4
bcxz
Output
Not Good String 
*/
#include <stdio.h>
#include <stdlib.h>

int main() {
    int n, i, c = 1;
    char  * s, * r;
    scanf("%d\n", &n);
    s = (char *)malloc((n + 1) * sizeof(char));
    r = (char *)malloc((n + 1) * sizeof(char));
    for(i = 0; i < n; i++)
        scanf("%c", (s + i));
    *(s + n) = '\0';    
    c = 1;
    for(i = 0; i < n; i++){
        *(r + n - 1 - i) = *(s + i);
    }
    for(i = 1; i < n; i++){
        if(abs(*(s + i) - *(s + i - 1)) != abs(*(r + i) - *(r + i - 1))){
            c = -1;
            break;
        }
    }
    if(c == 1)
        printf("Good String");
    else
        printf("Not Good String");
    return 0;
}