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


int main()
{int m,n,mat[100][100],x,y,k,i,i0=0,j0=0,j,a,b,deg_good=0;
scanf("%d",&m);
scanf("%d",&n);
for(x=0;x<m;x++)
{   for(y=0;y<n;y++)
      {scanf("%d",&mat[x][y]);
      }
}

for(k=1;k<=m&&k<=n;k++)
{
    for(i=m-k;i>=0;i--)
    {
        for(j=n-k;j>=0;j--)
        {int count1=0;int count2=0;
            for(a=i;a<i+k;a++)
            {
                for(b=j;b<j+k;b++)
                {
                    if((b-a==j-i)&&(mat[a][b]==1))
                    count1++;
                    if((b-a!=j-i)&&(mat[a][b]==0))
                    count2++;
                }
            }
            if((count1==k)&&(count2==k*(k-1))&&(k>=deg_good))
            {deg_good=k;i0=i;j0=j;}
        }
    }
}
if(deg_good!=0)printf("%d %d %d",deg_good,i0+1,j0+1);
else printf("0 -1 -1");
    return 0;
}