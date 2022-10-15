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

int main() {
	int a[100][100],m,max,n,i,j,sum[100];
	scanf("%d %d",&n,&m);
	for(i=0;i<n;i++)
	{
	    for(j=0;j<m;j++)
	    scanf("%d",&a[i][j]);
	}
	for(i=0;i<n;i++)
	{
	    sum[i]=0;
	    for(j=0;j<m;j++)
	    {
	        sum[i]=(sum[i]+a[i][j]);
	    }
	}
	max=sum[0];
	for(i=1;i<n;i++)
	{
	    if(sum[i]>sum[i-1])
	    max=sum[i];
	}
	int p[100],z=0;
	for(i=0;i<n;i++)
	{
	    if(sum[i]==max)
	    {
	    p[z]=i;
	    z++;
	    }
	}
         for(i=0;i<z;i++)
         printf("%d ",p[i]);
	return 0;
}