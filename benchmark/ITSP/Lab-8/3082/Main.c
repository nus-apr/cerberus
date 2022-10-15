/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
-----------------------------------------------------------------------------------------------------------

Given a matrix M[n][m], find out the row which has the maximum sum. If there are more than one row having maximum sum, print all of them in ascending order. The rows are indexed from 0.

Constraints:
n and m are between 1 to 100.

Input: 
The first line contains two integers n and m, which denote the dimension of the matrix.
Next there are n lines having m integers each. Each line denotes a row of the matrix and the ith value in jth line denotes the value of matrix[i][j].

Output:
A single line with the row number(or numbers) in ascending order separated by a single space.
*/
#include <stdio.h>
#include <limits.h>
int main()
{
    int n,m;
    scanf("%d %d",&n,&m);
    int mat[n][m];
    for(int i=0;i<n;i++)
    {
        for(int j=0;j<m;j++)
        {
            scanf("%d",&mat[i][j]);
        }
    }
    int ct=0;
    int row[n];
    int max=INT_MIN;
    for(int i=0;i<n;i++)
    {
        int sum=0;
        for(int j=0;j<m;j++)
        {
            sum+=mat[i][j];
        }
        if(sum > max)
        {
            max=sum;
            row[0]=i;ct=1;
        }
        else if(sum==max)
        {
            row[ct]=i;ct++;
        }
    }
    for(int i=0;i<ct;i++)
    {
        printf("%d ",row[i]);
    }
    printf("\n");
}