/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for nontrivial code
- Indentation: align your code properly
- Function use and modular programming
- Do not include anything in the header other than what is already given in the template. --------------------------------------------------------------------------------------------------------------

We say that a matrix is good if it has got a sub-matrix which is a symmetric matrix.  If a matrix is not good, then we say its goodness is 0. However, if it is good, we define goodness to be the dimension of largest symmetric sub-matrix of the given matrix (i.e. if the largest symmetric sub-matrix is n x n, then the goodness is n). For example,

0 1 1 0
1 0 0 1
1 0 2 3

This matrix is good since 
1 0
0 1
is its sub-matrix and is symmetric.

0 1 1
1 0 0
1 0 2
 is also a symmetric sub-matrix of the given matrix.

Since the dimension of the largest sub-matrix of the given matrix is 3, the goodness is 3.

Your task:
Given a matrix, print its goodness value and the location of the top left corner of the largest symetric sub-matrix. For the example given above, goodness value is 3 and location of the top left corner of the symmetric sub-matrix is (1,1) i.e. first row first column. If goodness is 0, then top left corner location may be taken as (-1,-1) since it is actually not defined.


Assume all numbers to be integer. If their are two or more largest symmetric sub-matrix with the location of top-left corner at (i1,j1) and (i2,j2), then output (i1,j1) if (i1 < i2) or (i1 == i2 and j1 < j2) , otherwise output (i2,j2).

Input:
m,n //denoting the number of rows and columns of the input matrix
followed by m x n matrix with m rows (each in a new line) and n columns
e.g.

3 4
0 1 1 0
1 0 0 1
1 0 2 3

Output:
g i j // if g is your goodness value and (i,j) is the location of the top left corner of the symmetric sub-matrix.

e.g. answer for the above input will be

3 1 1
*/
#include <stdio.h>
int min(int a, int b)
{
    return (a<b) ? a : b;
}
int main()
{
    int m,n,i,j,k,l,ans_i=-1,ans_j=-1,flag;
    int max_goodness = 0,curr_goodness, max_gp;
    scanf("%d%d",&m,&n);
    
    int M[m][n];
    
    for(i=0;i<m;i++)
    {
        for(j=0;j<n;j++)
        {
            scanf("%d",&M[i][j]);
        }
    }
    
    for(i=0;i<m;i++)
    {
        for(j=0;j<n;j++)
        {
            //checking whether an symmetric sub matrix begin at (i,j)                                        i.e. at i+1th row and j+1th column
            curr_goodness = 0;
            flag = 0;
            max_gp = min(m-i,n-j);
            for(k=0;k<max_gp;k++)
            {
                for(l=k;l>=0;l--)
                {
                    if(l==0)
                    {
                       continue;
                        
                    }
                    else
                    {
                        if(M[i+k][j+k-l] != M[i+k-l][j+k])
                        {
                            curr_goodness = k;
                            flag = 1;
                            break;
                        }
                    }
                }
                if(flag == 1)
                    break;
            }
            
            if (k == max_gp)
                curr_goodness = max_gp;

            if(curr_goodness > max_goodness)
            {
                max_goodness = curr_goodness;
                ans_i = i+1;
                ans_j = j+1;
                // printf("%d %d %d\n",ans_i,ans_j,max_goodness );
            }
        }
    }
    printf("%d %d %d\n", max_goodness, ans_i,ans_j );
    
}