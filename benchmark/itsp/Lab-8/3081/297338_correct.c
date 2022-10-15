/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"3 4
0 1 1 0
1 0 0 1
1 0 2 3", ExpOutput:"2 1 3
", Output:"2 1 3"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 0 1 0
0 0 0 0 1", ExpOutput:"5 1 1
", Output:"5 1 1"
Verdict:ACCEPTED, Visibility:1, Input:"2 2
0 2
3 4", ExpOutput:"0 -1 -1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:1, Input:"1 1
0", ExpOutput:"0 -1 -1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
3 2 3 4 5
1 2 3 4 5
6 7 8 9 10
11 23 5 5 5
-1 2 3 4 5", ExpOutput:"1 2 1
", Output:"1 2 1"
Verdict:ACCEPTED, Visibility:0, Input:"5 2
1 0
0 1
0 0
1 0
0 1", ExpOutput:"2 1 1
", Output:"2 1 1"
Verdict:ACCEPTED, Visibility:0, Input:"1 1
1", ExpOutput:"1 1 1
", Output:"1 1 1"
Verdict:ACCEPTED, Visibility:0, Input:"10 10
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
0 1 0 0 0 0 0 0 0 0
0 0 1 0 0 0 0 0 0 0", ExpOutput:"3 8 1
", Output:"3 8 1"
*/
#include <stdio.h>

/* prg to identify size and location of sub-matrix */

int largest_i(int a[100][100], int p)
{
    int i, j, max, row, column;
    max=0;
    for(i=0; i<p; i++)
    {
        for(j=0; j<p; j++)
        {
            if(max<a[i][j])
            {
                max = a[i][j];
                row = i;
                column = j;
            }
        }
    }
    if(max == 0)
    {
        printf("%d %d %d", max, -1, -1);
    }
    else
    {
        printf("%d %d %d", max, (row+1), (column+1));
    }
    return 0;
}

int check_identity(int mat[100][100], int sub_mat[100][100], int m, int n)
{
    int i, j, k, p, r, s, count;
    int a[100][100];
    p = (m>n?n:m);
    for(i=1; i<=p; i++)
    {
        int row = 0;
        while((row<m))
        {
            int column = 0;
            while(column<n)
            {
                count = 0;
                for(r=0, j=row;r<i && j<(row+i) && j<m; r++, j++)
                {
                    for(s=0, k=column; s<i && k<(column+i) && k<n; s++, k++)
                    {
                        if(mat[j][k] == sub_mat[r][s])
                        {
                            count+=1;
                        }
                    }
                }
                if(count == (i*i))
                {
                    a[row][column]=i;
                }
                column+=1;
            }
            row+=1;
        }
    }
    largest_i(a, p);
    return 0;
}

int main()
{
    int mat[100][100], sub_mat[100][100], i, j, m, n;
    for(i=0; i<100; i++)
    {
        for(j=0; j<100; j++)
        {
            mat[i][j] = 0;
            sub_mat[i][j] = 0;
            if(i == j)
            {
                sub_mat[i][j] = 1;
            }
        }
    }
    scanf("%d %d", &m, &n);
    for(i=0; i<m; i++)
    {
        scanf("\n%d", &mat[i][0]);
        for(j=1; j<n; j++)
        {
            scanf(" %d", &mat[i][j]);
        }
    }
    check_identity(mat, sub_mat, m, n);
    
    return 0;
}