/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for the non trivial part of the code
- Indentation: align your code properly
---------------------------------
Given an input N(N>0), your program should output the Nth tetrahedral number. To calculate the nth tetrahedral number, T(n), the formula is as following:
T(n) = (1) + (1+2) + (1+2+3) + (1+2+3+4) + ... + (1+2+3+4+...+n)
Example:
Input:
2
Output:
4

Input:
5
Output:
35
*/
#include <stdio.h>
int main()
{
    int i,j,n,sum=0;
    scanf("%d",&n);
    for(i=1;i<=n;i++)
    {
        for(j=1;j<=i;j++)
        {
            sum+=j;
        }
    }
    printf("%d",sum);
    return 0;
}
 