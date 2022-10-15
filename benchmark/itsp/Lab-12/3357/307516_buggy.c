/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 0 4
1 1 3", ExpOutput:"YES
", Output:"Yes"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 0 4
10 10 3", ExpOutput:"NO
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"-1 -1 5
6 6 5", ExpOutput:"YES
", Output:"Yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -1 1
5 -1 1", ExpOutput:"NO
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2 2 2
2 2 1", ExpOutput:"YES
", Output:"Yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 0 3
-4 0 3", ExpOutput:"NO
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 0 1
3 0 3", ExpOutput:"YES
", Output:"Yes"
*/
#include<stdio.h>
#include<stdlib.h>
struct circle//defining data structure
{
    int x;
    int y;
    int r;
};
int main()
{
    float p,q,m;
    struct circle one;//data structure for first circle
    struct circle two;
    scanf("%d",&one.x);//scanning x coordinate of circle
     scanf("%d",&one.y);
      scanf("%d",&one.r);
       scanf("%d",&two.x);
        scanf("%d",&two.y);
         scanf("%d",&two.r);
        // m=[((one.x)-(two.x))*((one.x)-(two.x))+((one.y)-(two.y))*((one.y)-(two.y))]
         
        // q=[(one.r)+(two.r)]
         if(((one.x)-(two.x))*((one.x)-(two.x))+((one.y)-(two.y))*((one.y)-(two.y))>(((one.r)+(two.r))*((one.r)+(two.r))))
         {
             printf("No");
             
         }
         else
         {
             printf("Yes");
         }
}