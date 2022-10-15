/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"1 10 4 1
2 9 3 2", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"3 7 7 3
4 5 5 4", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"0 5 5 0
3 7 5 6", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 6 0
3 3 5 0", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 6 0
7 3 10 0", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"-5 -5 -2 -10
5 5 10 2", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"0 0 5 -5
1 -1 4 -4", ExpOutput:"YES
", Output:"YES"
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
//printf("i=%d j=%d\n",i,j);
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