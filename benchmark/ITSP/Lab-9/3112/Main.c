/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.

- You have to solve this problem using recursion 
- Some marks are reserved for writing correct base case and recursive step  
-----------------------------------------------------------------------------------------------------------

A string is said to be well-ordered if all the characters (lower-case English Alphabet) in the sequence are in lexicographic order and there is no repetition. So, "ahs" is a well-ordered string, whereas "ahe" and "ahh" are not.
Given two numbers $n$ and $k$, you have to print all possible well-ordered strings of length $k$ comprising of characters from first $n$ lower-case English alphabets.
Assume : $ 1 \le k \leq n \le 26 $
Each of these strings should be printed in a new line, and also in lexicographical order, i.e "abc" should be printed before "abd" which in turn should be printed before "bcd".

Input : 
3 1
Output :
a
b
c

Input : 
4 2
Output :
ab
ac
ad
bc
bd
cd
*/
#include <stdio.h>
 
void printArr(char arr[], int k)
{
    int i;
    for (i=0; i<k; i++)
        printf("%c", arr[i]);
    printf("\n");
}

void printSeq(int n, int m, int len, char arr[])
{
    if(len == m)
        printArr(arr, m);
    char last_element = len==0?'a'-1:arr[len-1];
    if(last_element >= 'a'-1+n)
        return;
    
    char i;
    for(i = last_element+1; i<='a'-1+n; i++)
    {
        arr[len] = i;
        printSeq(n, m, len+1, arr);
    }
}

 
int main()
{
    int k, n;
    scanf("%d%d", &n, &k);
    char arr[k];
    printSeq(n, k, 0, arr);
    return 0;
}