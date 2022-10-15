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
int main(){
    int d;
    scanf("%d ", &d);
    int N;
    scanf("%d\n", &N);
    int i;
    int b[20];
    for(i=0; i<d; i=i+1)
        scanf("%d", &b[i]);
    int a[30];
    for(i=0; i>=0&&i<d; i=i+1){
        a[i]=b[i];
    }
    //printf("%d\n",a[3]);
    for(i=d; i<=N; i=i+1){
      int sum;
      sum=0;
      int c;
      c=i-d;
      int j;
      for(j=i-1;j>=c;j--)
        sum=sum+a[j];
      a[i]=sum;
    }
    printf("%d", a[N]);
	return 0;
}