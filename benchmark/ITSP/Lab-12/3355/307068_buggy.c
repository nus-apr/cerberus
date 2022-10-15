/*numPass=3, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 10
-1 6", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 3", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10 20
20 50", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 0
-1 0", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -5
-6 9", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 1
1 10", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"7 9
2 3", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 10
5 7", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"8 10
5 7", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>

struct data
{
    int left_index;
    int right_index;
};
int main() {
  int x;
  int l1, l2; int r1, r2; 
  
  scanf("%d %d", &l1, &r1);
  scanf("%d %d", &l2, &r2);
  
  struct data index1= {l1,r1};
  struct data index2= {l2,r2};
  
  x=((index1.right_index<index2.left_index)||(index2.right_index<index1.left_index))?1:0;
  
  if (x=1)
  {
      printf("NO");
  }
    else
    printf("YES");
    
    return 0;
}

//MY ALGO//

//first i made a structure containing two data, one is for left hand digit and right hand digit of a given interval... 
//if the interval_1 either lies completely in right handed side or in complete left handed side then my code is printing "NO" otherwise "YES"... hence if interval is(l1,r1)&(l2,r2);
//then if "r1<l2-OR-r2<l1" then interval is completely isolated and hence printing the desired result.