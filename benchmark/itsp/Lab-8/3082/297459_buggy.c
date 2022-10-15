/*numPass=4, numTotal=5
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
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 5
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
", ExpOutput:"0 1 2 3 4 
", Output:"0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99 "
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
    for(j=0;j<100;j++)
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