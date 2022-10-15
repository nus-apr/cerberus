/*numPass=5, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 0 4
1 1 3", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"0 0 4
10 10 3", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"-1 -1 5
6 6 5", ExpOutput:"YES
", Output:"NO"
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
#include<stdlib.h>
#include<math.h>
struct def_circle
{
    int x;
    int y;
    int r;
};
typedef struct def_circle circle;
circle* newCircle(int a,int b,int radius)
{
    circle* c1=(circle*)malloc(sizeof(circle));
    c1->x=a;
    c1->y=b;
    c1->r=radius;
    return c1;
}
int checkOverlap(circle* c1,circle* c2)
{
    int disSq=((c1->x-c2->x)*(c1->x-c2->x)+(c1->y-c2->y)*(c1->y-c2->y));
    if(disSq<=abs(c1->r-c2->r)*abs(c1->r-c2->r))
     return 1;
    else
     return 0;
    
}
int main()
{
    int x1,y1,r1;
    scanf("%d %d %d",&x1,&y1,&r1);
    circle* c1=newCircle(x1,y1,r1);
    scanf("%d %d %d",&x1,&y1,&r1);
    circle* c2=newCircle(x1,y1,r1);
    //printf("%d %d",c1->r,c2->r);
    int ch=checkOverlap(c1,c2);
    if(ch==1) printf("YES");
    else printf("NO");
    return 0;
}