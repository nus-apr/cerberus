/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.

- You have to solve this problem using recursion 
- Some marks are reserved for writing correct base case and recursive step  
-----------------------------------------------------------------------------------------------------------
Given two positive integers $n$ and $m$, print all increasing sequences of length $m$ such that the elements in every sequence are from first $n$ natural numbers.
Assume : $ 1 \le m \leq n \le 50 $. 
You should print the sequences in lexicographical order.

Input :
3 2
Output :
1 2
1 3
2 3

Input : 
4 1
Output :
1
2
3
4
*/
#include <stdio.h>
 
void printArr(int arr[], int m)
{
    int i;
    for (i=0; i<m; i++)
        printf("%d ", arr[i]);
    printf("\n");;
}

void printSeq(int n, int m, int len, int arr[])
{
    if(len == m)
        printArr(arr, m);
    int last_element = len==0?0:arr[len-1];
    if(last_element >= n)
        return;
    
    int i;
    for(i = last_element+1; i<=n; i++)
    {
        arr[len] = i;
        printSeq(n, m, len+1, arr);
    }
}

 
int main()
{
    int m, n;
    scanf("%d%d", &n, &m);
    int arr[m];
    printSeq(n, m, 0, arr);
    return 0;
}
