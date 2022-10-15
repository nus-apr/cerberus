/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:"47
55
56
"
Verdict:ACCEPTED, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"13
20
20
"
Verdict:ACCEPTED, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"10
14
18
"
Verdict:ACCEPTED, Visibility:0, Input:"8
2 4 6 8 10 11 12 14
6", ExpOutput:"41
51
61
", Output:"41
51
61
"
Verdict:ACCEPTED, Visibility:0, Input:"7
2 4 -1 -5 2 5 6
4", ExpOutput:"0
0
1
8
", Output:"0
0
1
8
"
*/
#include <stdio.h>
int main() {
    int s;
    scanf("%d",&s);
    int arr[20],j,i,k,p,sum=0;
    for(i=0;i<s;i++){
      scanf("%d",&arr[i]);
    }
      scanf("%d",&k);
      for(j=0;j<=s-k;j++){
          sum=0;
          for(p=j;p<j+k;p++)
      sum=sum + arr[p];
         printf("%d\n",sum);
    }
	 
	    return 0;
}