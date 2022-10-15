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

void swap(int *a, int *b)
{
    int *tmp;
    *tmp=*a;
    *a=*b;
    *b=*tmp;
}


struct point
{
    int x; 
    int y;
};

struct rect
{
    struct point a;
    struct point b;
};

int overlap(struct rect r1, struct rect r2)
{
    if (r1.a.x>r1.b.x)
        swap(&r1.a.x, &r1.b.x);
    if (r1.a.y<r1.b.y)
        swap(&r1.a.y, &r1.b.y);
    if (((r2.a.x>=r1.a.x&&r2.a.x<=r1.b.x)&&
         (r2.a.y<=r1.a.y&&r2.a.y>=r1.b.y))||
        ((r2.b.x>=r1.a.x&&r2.b.x<=r1.b.x)&&
         (r2.b.y<=r1.a.y&&r2.b.y>=r1.b.y)))
        return 1;
    else
        return 0;
}

int main() 
{
    struct rect r1, r2;
    scanf ("%d %d", &r1.a.x, &r1.a.y);
    scanf ("%d %d", &r1.b.x, &r1.b.y);
    scanf ("%d %d", &r2.a.x, &r2.a.y);
    scanf ("%d %d", &r2.b.x, &r2.b.y);
    if (overlap(r1, r2)||overlap(r2, r1))
        printf ("YES");
    else
        printf ("NO");
    return 0;
}