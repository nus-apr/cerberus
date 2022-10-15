/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"3
1 1
2 3
4 5", ExpOutput:"no
", Output:"no"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 1
2 3
4 6
7 0", ExpOutput:"yes
", Output:"yes"
Verdict:ACCEPTED, Visibility:0, Input:"4
0 0
4 5
5 4
3 6", ExpOutput:"no
", Output:"no"
Verdict:ACCEPTED, Visibility:0, Input:"4
1 2
5 4
4 7
0 0", ExpOutput:"yes
", Output:"yes"
*/
#include <stdio.h>

int main()
{
    int mat[8][8] = {};         //declaring matrix with all elements 0
    int n, i, j, k, r, c;       //declaring variables
    scanf ("%d", &n);           //scanning input
    for (i=0; i<n; i++)
    {
        scanf ("%d %d\n", &r, &c);
        mat[r][c] = 1;          //initialising boxes with queen to 1
        k=c;
        for (j=0; j<8; j++)
        {
            if (mat[j][k]==1&&j!=r)
            {                   //checking column for another queen 
                printf ("no");
                return 0;
            }
        }
        j=r;
        for (k=0; k<8; k++)
        {                       //checking row for another queen
            if (mat[j][k]==1&&k!=c)
            {
                printf ("no");
                return 0;
            }
        }
        k=c-1;
        for (j=r-1; j>=0&&k>=0; j--)
        {                       //checking upper diagonal
            if (mat[j][k]==1)
            {
                printf ("no");
                return 0;
            }
        k=k-1;    
        }
        k=c+1;
        for (j=r+1; j<8&&k<8; j++)
        {                       //checking lower diagonal
            if (mat[j][k]==1)
            {
                printf ("no");
                return 0;
            }    
        k=k+1;
        }
        k=c-1;
        for (j=r+1; j<8&&k>=0; j++)
        {
            if (mat[j][k]==1)
            {
                printf ("no");
                return 0;
            }
        k=k-1;
        }
        k=c+1;
        for (j=r-1; j>=0&&k<8; j--)
        {
            if (mat[j][k]==1)
            {
                printf ("no");
                return 0;
            }
        k=k+1;
        }
    }
    printf ("yes");             //printing yes if no queen found in     `                                restricted region
	// Fill this area with your code.
	return 0;
}