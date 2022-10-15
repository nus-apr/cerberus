/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"0 0 4
1 1 3", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"0 0 4
10 10 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"-1 -1 5
6 6 5", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"-1 -1 1
5 -1 1", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"2 2 2
2 2 1", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"3 0 3
-4 0 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"1 0 1
3 0 3", ExpOutput:"YES
", Output:"YES"
*/
#include<stdio.h>
struct cir{
           int x;
           int y;
           int r;
          };
int main()
{
 struct cir a;
 struct cir b;
 scanf("%d",&a.x);
 scanf("%d",&a.y);
 scanf("%d",&a.r);
 scanf("%d",&b.x);
 scanf("%d",&b.y);
 scanf("%d",&b.r);
 if(((a.r+b.r)*(a.r+b.r))<=(((a.x-b.x)*(a.x-b.x))+((a.y-b.y)*(a.y-b.y))))
 {
     printf("NO"); 
 }
 else
 {
     printf("YES");
 }
 return 0;    
}