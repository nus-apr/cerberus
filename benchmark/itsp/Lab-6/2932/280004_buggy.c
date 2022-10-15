/*numPass=2, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"10"
Verdict:ACCEPTED, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"55"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"343275"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"-22606"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"29"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"1578448567"
Verdict:WRONG_ANSWER, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:"-4895"
*/
#include <stdio.h>
int main() {
  int sum=0,d,N,a[100],b[100];
  scanf("%d %d",&d,&N);
  for(int i=0;i<d;i++)
     scanf("%d",&b[i]);
  if(N<d)
      {
    for(int i=0;i<=N;i++)
      {a[i]=b[i];}
      printf("%d",a[N]);
      }
  else
     {   int i;
         for(i=0;i<d;i++)
         {a[i]=b[i];}
         for(i=d;i<=N;i++)
         {for(int j=1;j<=d;j++)
          sum=sum+a[i-j];
         a[i]=sum;}     
      printf("%d",a[N]);
     }
      return 0;
}