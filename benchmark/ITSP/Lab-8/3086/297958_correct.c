/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"5 8
0 1 0 1 0 1 0 1
0 0 0 0 0 0 0 0
0 0 0 1 1 1 0 0
0 0 0 1 1 1 0 0
0 0 0 1 1 1 0 0", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"4 3
1 1 1 
1 1 1
1 1 1
1 1 1
", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"3 3
0 0 0
0 0 0
0 0 0", ExpOutput:"0
", Output:"0"
Verdict:ACCEPTED, Visibility:0, Input:"2 5
0 0 0 0 0
1 1 1 1 1", ExpOutput:"1
", Output:"1"
Verdict:ACCEPTED, Visibility:0, Input:"2 5
0 1 0 1 0
1 0 1 0 1", ExpOutput:"1
", Output:"1"
*/
#include <stdio.h>

int n,m;
void nm( int input[100][100]);
int mini(int a,int b,int c);

int main() 
{
scanf("%d%d",&n,&m);
int x[100][100];
for(int i=0;i<n;i++)
 for(int j=0;j<m;j++)
   
       scanf("%d",&x[i][j]);
    
       
   
   

nm(x);
	return 0;
}
void nm( int input[100][100])
{ int i,sum[100][100];
    for(int j=0;j<m;j++)
        sum[0][j]=input[0][j];
    for (int j=0;j<n;j++)
        sum[j][0]=input[j][0];
 
    for(i=1;i<n;i++)
   { for(int j=1;j<m;j++)
    {
        if(input[i][j]==0)
            sum[i][j]=0;
        else if(input[i][j]==1)
            sum[i][j]=1+mini(sum[i-1][j],sum[i][j-1],sum[i-1][j-1]);
        
    }
   }
   
   int max=sum[0][0];
   for(int i=0;i<n;i++)
   {for(int j=0;j<m;j++)
   if(max<=sum[i][j])
   max=sum[i][j];
   }
   printf("%d",max);
}
 int mini(int a,int b,int c)

 { int min;
if(a<=b && a<=c)
   min=a;
   if (b<=a && b<=c)
  min=b;
  if(c<=a && c<=b)
  min=c;
  return min;
 }