/*numPass=4, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 10 4 1
2 9 3 2", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 7 7 3
4 5 5 4", ExpOutput:"YES
", Output:"NO"
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 0 5 -5
1 -1 4 -4", ExpOutput:"YES
", Output:"NO"
*/
#include <stdio.h>
#include<stdlib.h>
struct point
{
    int x,y;
};
typedef struct point Point;
struct rect
{
    Point lefttop, leftbot;
    Point rightbot, righttop;
 // int lefttop_x,lefttop_y,rightbot_x,rightbot_y;
};
typedef struct rect Rect;
int lies_ins(Point a, Rect b)
{
    int x_in_range=0, y_in_range=0;
    if(a.x>=b.lefttop.x&&a.x<=b.rightbot.x)
        x_in_range=1;
    if(a.y>=b.rightbot.y&&a.y<=b.lefttop.y)
        y_in_range=1;
    if(x_in_range&&y_in_range) return 1;
    else return 0;
}
void overlap(Rect *r1, Rect *r2)
{
    if(lies_ins(r1->lefttop, *r2)+lies_ins(r1->righttop, *r2)+lies_ins(r1->leftbot,*r2)+lies_ins(r1->rightbot,*r2))
    printf("YES");
    else printf("NO");
}
int main() 
{
    Rect *r1, *r2;
    r1=(Rect*)malloc(sizeof(Rect));
    r2=(Rect*)malloc(sizeof(Rect));
    scanf("%d %d %d %d", &r1->lefttop.x,&r1->lefttop.y,&r1->rightbot.x,          &r1->rightbot.y);
    scanf("%d %d %d %d", &r2->lefttop.x,&r2->lefttop.y,&r2->rightbot.x,          &r2->rightbot.y);
    r1->leftbot.x=r1->lefttop.x;
    r1->leftbot.y=r1->rightbot.y;
    r1->righttop.x=r1->rightbot.x;
    r1->righttop.y=r1->lefttop.y;
    r2->leftbot.x=r2->lefttop.x;
    r2->leftbot.y=r2->rightbot.y;
    r2->righttop.x=r2->rightbot.x;
    r2->righttop.y=r2->lefttop.y;
    overlap(r1, r2);
    return 0;
}