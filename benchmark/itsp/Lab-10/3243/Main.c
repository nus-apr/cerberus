/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for non-trivial code 
- Indentation: align your code properly 
- Function use and modular programming 
- Do not include anything in the header other than what is already given in the template. 
- Use pointers only and when required allocate memory Dynamically instead of static memory allocation otherwise you will get 0 marks.
------------------------------------------------------------------------------------------------------------------------------------------------
Given a string w, rearrange the letters of w to construct another string s in such a way that s is lexicographically greater than w. If there is no bigger string for given input then print "No Answer". In case of multiple possible answers, find the lexicographically smallest one and print that string. Lexicographic order is as follows 'a' < 'b', "aa" < "ab", "ab" < "da", "dac" < "dca".

Note : string will contain lower case alphabets only. Size of string will be given by the user and use dynamic memory allocation.

Input Format : First Line will contain the size of the string and next line will contain string itself.
Output Format : Print the lexicographically smallest string out of all lexicographically bigger strings possible.

Example
Input 
2
ab
Output
ba 
*/
#include <stdio.h>
#include <stdlib.h>

int main(){
    int n;
    scanf("%d\n", &n);
    char * s = (char *)malloc((n + 1) * sizeof(char));
    for(int i = 0; i < n; i++)
        scanf("%c", (s + i));
    *(s + n) = '\0';    
    int * a = (int *)calloc(n, sizeof(char));
    for(int i = 0; i < n; i++)
        *(a + i) = *(s + i) - 'a';
    int i = n - 1;
    while(i > 0 && *(a + i - 1) >= *(a + i))
        i--;
    if(i <= 0){
        printf("No Answer");
    }
    else{
        int l = n - 1;
        while(*(a + l) <= *(a + i - 1))
            l--;
        int tmp = *(a + i - 1);
        *(a + i - 1) = *(a + l);
        *(a + l) = tmp;
        l = n - 1;
        while(i < l){
            tmp = *(a + i);
            *(a + i) = *(a + l);
            *(a + l) = tmp;
            i++;
            l--;
        }
        for(i = 0; i < n; i++)
            *(s + i) = *(a + i) + 'a';
        printf("%s", s);    
    }
    return 0;
}