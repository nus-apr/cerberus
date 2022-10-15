/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
-----------------------------------------------------------------------------------------------------------
There is a matrix nxm which consists of only zeroes and ones. You need to find out the size of the largest square in the matrix which is comprised of only 1s.
Say the matrix is
01010101
00000000
00011100
00011100
00011100
In this case the size of the largest square is 3 [the square's leftmost topmost point being (2,3)].

Input:
Two integers: n and m.
This denotes that the matrix has n rows and m columns.
Next there will be n lines having m integers each. (denoting the elements of the matrix).

Output:
An integer denoting the size of the largest square.

Hint: Create another matrix sum[n][m].Copy the first row and first column of the original matrix(let us call this matrix input[n][m]).Now traverse through all the other elements of input[][].
 If input[i][j]==0 then sum[i][j]=0.
If input[i][j]==1 then sum[i][j]=1+min(sum[i-1][j],sum[i][j-1],sum[i-1][j-1]);

After creating the sum[][],the maximum element in this matrix is the answer.

*/
#include <stdio.h>
#include <string.h>
#include <math.h>
int main()
{
    int n,m;
    scanf("%d %d",&n,&m);
    int dp[n][m],mat[n][m];
    memset(dp,0,sizeof(dp));
    for(int i=0;i<n;i++)
    {
        for(int j=0;j<m;j++)
        {
            scanf("%d",&mat[i][j]);
            if(i==0 || j==0)
            {
                dp[i][j]=mat[i][j];
            }
        }
    }
    int max=0;
    if ((m == 1) && (n == 1)) {
        printf("%d\n", mat[0][0]!=0);
        return 0;
    }
    for(int i=1;i<n;i++)
    {
        for(int j=1;j<m;j++)
        {
            if(mat[i][j]==0)continue;
            int m1;
            if(dp[i][j-1]<dp[i-1][j])
                m1=dp[i][j-1];
            else
                m1=dp[i-1][j];
            if(m1 > dp[i-1][j-1])
                m1=dp[i-1][j-1];
            m1++;
            dp[i][j]=m1;
            if(m1>max)max=m1;
          
        }
    }
    printf("%d\n",max);
    
    return 0;
}
