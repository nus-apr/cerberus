/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 3
1 1 1
1 1 1
1 1 1", ExpOutput:"0 1 2 
", Output:"


0 1 2 "
Verdict:ACCEPTED, Visibility:1, Input:"3 4
1 2 3 4
10 20 17 15
-10 -19 -2 -1", ExpOutput:"1 
", Output:"


1 "
Verdict:ACCEPTED, Visibility:1, Input:"5 5
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
", ExpOutput:"0 1 2 3 4 
", Output:"




0 1 2 3 4 "
Verdict:ACCEPTED, Visibility:0, Input:"3 3
-1 -2 -3
-4 -5 -6
-7 -8 -9", ExpOutput:"0 
", Output:"


0 "
Verdict:ACCEPTED, Visibility:0, Input:"3 3 
-1 -1 -1
-1 -1 -1
-1 -1 -1", ExpOutput:"0 1 2 
", Output:"


0 1 2 "
*/
#include <stdio.h>
int R_Sum(int M1[100][100],int row,int clm)//Fuction for calculating sum of Row
{
    int i,j,rsum;
    for(i=0;i<row;i++)
    {
        rsum=0;
        for(j=0;j<clm;j++)
        {
            rsum=rsum+M1[i][j];
        }
    }
    return rsum;
}
int main() {
	int M[100][100],m,n,max,rmax;
	scanf("%d %d\n",&n,&m);
	for(int i=0;i<n;i++)//Initialising the Matrix
	{
	    for(int j=0;j<m;j++)
	    {
	        scanf("%d",&M[i][j]);
	    }
	    printf("\n");
	}
	max=R_Sum(M,1,m);
	for(int i=1;i<n;i++)//Finding row having maximum sum
	{
	    if(max<R_Sum(M,(i+1),m))
	    {
	        max=R_Sum(M,(i+1),m);
	    }
	}
	for(int i=1;i<=n;i++)
	{
	    if(max==R_Sum(M,i,m))
	    printf("%d ",(i-1));
	}
	return 0;
}