/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:"47
55
56
16
6
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"13
20
20
4
6
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"10
14
18
4198544
4198540
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
2 4 6 8 10 11 12 14
6", ExpOutput:"41
51
61
", Output:"41
51
61
61
61
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
2 4 -1 -5 2 5 6
4", ExpOutput:"0
0
1
8
", Output:"0
0
1
8
13
15
"
*/
#include <stdio.h>

int main() {
      int i=0; int n,k;
      scanf("%d\n",&n);
      int s[n];
      while(i<n) {
         scanf("%d ",&s[i]);
         i=i+1;
      }
      scanf("\n%d",&k);
      int l,j;
      for(j=2;j<=(n-k+4);j++) {
          int sum=0;
         for(l=j-2;l<(k+j-2);l++) {
           sum=sum+s[l];
         }
         printf("%d\n", sum);
  }
	return 0;
}
