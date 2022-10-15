/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"10"
Verdict:ACCEPTED, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"55"
Verdict:ACCEPTED, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"19457"
Verdict:ACCEPTED, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"-1365"
Verdict:ACCEPTED, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"8"
Verdict:ACCEPTED, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"55312397"
Verdict:ACCEPTED, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:"-341"
*/
#include <stdio.h>
int main() {
  int d,N,a[100],b[100];
  scanf("%d %d",&d,&N);
  for(int i=0;i<d;i++)
  {
     scanf("%d",&b[i]);
  }
  if(N<d)
      {
        int i;
        for( i=0;i<d;i++)
        {a[i]=b[i];}
        printf("%d",a[N]);
      }
  else
     {   int i;
         for(i=0;i<d;i++)
         {
             a[i]=b[i];
         }
         for(i=d;i<=N;i++)
         {   int sum=0;
             for(int j=1;j<=d;j++)
          sum=sum+a[i-j];
          a[i]=sum;}     
      printf("%d",a[N]);
      }
      return 0;
}