/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 3
1 1 1
1 1 1
1 1 1", ExpOutput:"0 1 2 
", Output:"0 1 2 "
Verdict:ACCEPTED, Visibility:1, Input:"3 4
1 2 3 4
10 20 17 15
-10 -19 -2 -1", ExpOutput:"1 
", Output:"1 "
Verdict:ACCEPTED, Visibility:1, Input:"5 5
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
", ExpOutput:"0 1 2 3 4 
", Output:"0 1 2 3 4 "
Verdict:ACCEPTED, Visibility:0, Input:"3 3
-1 -2 -3
-4 -5 -6
-7 -8 -9", ExpOutput:"0 
", Output:"0 "
Verdict:ACCEPTED, Visibility:0, Input:"3 3 
-1 -1 -1
-1 -1 -1
-1 -1 -1", ExpOutput:"0 1 2 
", Output:"0 1 2 "
*/
#include <stdio.h>
int maxs(int[],int);
int main()
{
    int n,m,i,j;
    scanf("%d %d",&n,&m);
    int a[100][100];
    for(i=0;i<n;i++)
    {
        for(j=0;j<m;j++)
        scanf("%d",&a[i][j]);
    }
    int sum[100];
    for(j=0;j<100;j++)
    sum[j]=0;
    for(i=0;i<n;i++)
    {
        for(j=0;j<m;j++)
        sum[i]=sum[i]+a[i][j];
    }
    int max=maxs(sum,n);
    for(j=0;j<n;j++)
    {
        if(sum[j]==max)
        printf("%d ",j);
    }
	return 0;
}
int maxs(int ar[],int l)
{
    int m=ar[0],i;
    for(i=0;i<l;i++)
    {
        if(ar[i]>m)
        m=ar[i];
    }
    return m;
}