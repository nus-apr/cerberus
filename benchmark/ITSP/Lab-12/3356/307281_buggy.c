/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 10 4 1
2 9 3 2", ExpOutput:"YES
", Output:"i=9 j=2
YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 7 7 3
4 5 5 4", ExpOutput:"YES
", Output:"i=5 j=4
YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 5 5 0
3 7 5 6", ExpOutput:"NO
", Output:"i=7 j=3
i=6 j=4
NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 6 0
3 3 5 0", ExpOutput:"YES
", Output:"i=3 j=3
YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 6 0
7 3 10 0", ExpOutput:"NO
", Output:"i=3 j=7
i=2 j=8
i=1 j=9
i=0 j=10
NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-5 -5 -2 -10
5 5 10 2", ExpOutput:"NO
", Output:"i=5 j=5
i=4 j=6
i=3 j=7
i=2 j=8
NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 0 5 -5
1 -1 4 -4", ExpOutput:"YES
", Output:"i=-1 j=1
YES"
*/
#include <stdio.h>

typedef struct{
    int x,y;
} point;

typedef struct{
    point left;
    point right;
} rect;
int main() {
    rect r1,r2;
    scanf("%d %d",&(r1.left.x),&(r1.left.y));
    scanf("%d %d",&r1.right.x,&r1.right.y);
    scanf("%d %d",&r2.left.x,&r2.left.y);
    scanf("%d %d",&r2.right.x,&r2.right.y);
    
    int i,j;
    for(i=(r2.left.y),j=(r2.left.x);
    i>=(r2.right.y) && j<=(r2.right.x);
    j++,i--)
    {
printf("i=%d j=%d\n",i,j);
        if(i<=r1.left.y && i>=r1.right.y 
          &&j>=r1.left.x && j<=r1.right.x)
        {
            printf("YES");
            return 0;
        }
    }
  /*  for(j=(r2.left.x);j<=(r2.right.x);j++)
    {
        printf("j=%d\n",j);
        if(j>=r1.left.x && j<=r1.right.x)
        {
            printf("YES");
            return 0;
        }
    }*/
    printf("NO");
    
  /*  printf("%d %d ",(r1.left.x),(r1.left.y));
    printf("%d %d\n",r1.right.x,r1.right.y);
    printf("%d %d ",r2.left.x,r2.left.y);
    printf("%d %d",r2.right.x,r2.right.y);*/
    
    return 0;
}