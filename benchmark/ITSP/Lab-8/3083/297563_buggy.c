/*numPass=5, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"3 4
0 1 1 0
1 0 0 1
1 0 2 3", ExpOutput:"3 1 1
", Output:"3 1 1"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 -1
0 0 0 1 0
0 0 -1 0 1", ExpOutput:"5 1 1
", Output:"5 1 1"
Verdict:ACCEPTED, Visibility:1, Input:"4 4
1 2 3 4
3 1 2 3
4 2 1 4
1 3 4 1", ExpOutput:"3 2 2
", Output:"3 2 2"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 2
0 1
-1 0", ExpOutput:"1 1 1
", Output:"0 1 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 1
0", ExpOutput:"1 1 1
", Output:"0 1 1"
Verdict:ACCEPTED, Visibility:0, Input:"5 5
3 2 3 4 5
1 2 0 0 5
6 0 8 0 10
11 0 0 5 5
-1 2 3 4 5", ExpOutput:"3 2 2
", Output:"3 2 2"
Verdict:ACCEPTED, Visibility:0, Input:"6 6
1 2 3 4 5 6
2 3 4 5 6 1
3 4 5 6 1 2
4 5 6 1 2 3
5 6 1 2 3 4
6 1 2 3 4 5", ExpOutput:"6 1 1
", Output:"6 1 1"
*/
#include <stdio.h>

int goodv(int m[][20], int ind[],  int r, int c);

int main()
{
    int mat[20][20], m, n;
    int g=0, i, j;
    int index[2];
    
    scanf("%d", &m);
    scanf("%d", &n);
    
    for(i=0; i<m; ++i)
        for(j=0; j<n; ++j)
            scanf("%d", &mat[i][j]);
    
    g = goodv( mat, index, m, n);
    
    printf("%d %d %d", g, index[0]+1, index[1]+1);
    
    return 0;
}

int goodv(int m[][20], int ind[],  int r, int c)
{
    int endi[2], i, j, k, k1, k2, maxg=0, tmpg;
    int tmpi[2];
    
    for(i=0; i<c; ++i)
    for(j=0; j<r;  ++j)
    {
        endi[0] = r-1;
        endi[1] = c-1;
    if(m[i+1][j]==m[i][j+1] && (i+1)<r && (j+1)<c)    
    {   tmpi[0] = k1 = i;
        tmpi[1] = k2 = j;
        tmpg=0;
        
        while( k1<endi[0] && k2<endi[1])
        {   
            k = 1;
        while( (((k1+k)<r)&&((k2+k)<c))&& (m[k1+k][k2]== m[k1][k2+k]) )
                k++;
        
            endi[0] = k1 + k-1;
            endi[1] = k2 + k-1;
            k1++;
            k2++;
        }
        
        tmpg = endi[0] - i +1;
        
        if( tmpg > maxg )
        {
            maxg = tmpg;
            ind[0] = tmpi[0];
            ind[1] = tmpi[1];
        }
        
        else if(tmpg == maxg)
             {
                if( ((tmpi[0]<ind[0])||(tmpi[0]==ind[0]))&&(tmpi[1]<ind[1]) )
                {
                    ind[0] = tmpi[0];
                    ind[1] = tmpi[1];
                }
             }
    } 
        }     
    return maxg;    
}