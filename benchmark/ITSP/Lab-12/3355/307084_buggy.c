/*numPass=8, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 6", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"10 20
20 50", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"0 0
-1 0", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -5
-6 9", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"0 1
1 10", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"7 9
2 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"1 10
5 7", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"8 10
5 7", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>
#include <stdlib.h>
    struct interval//defining interval
    {
        int x;
        int y;
    };
    typedef struct interval si;//shortcut
int main() {
    int a,b;
    si *i1,*i2;//defining two intervals
    i1=(si*)malloc(sizeof(si));
    i2=(si*)malloc(sizeof(si));
    scanf("%d %d",&a,&b);
    (*i1).x=a;
    (*i1).y=b;
    if((*i1).x>(*i1).y)
    {
        int t=(*i1).x;
        (*i1).x=(*i1).y;
        (*i1).y=t;
    }
    scanf("%d %d",&a,&b);
    (*i2).x=a;
    (*i2).y=b;
    if((*i2).x>(*i2).y)
    {
        int t=(*i2).x;
        (*i2).x=(*i2).y;
        (*i2).y=t;
    }
     //printf("%d %d",(*i1).x,(*i1).y);
    if((((*i2).x>=(*i1).x)&&((*i2).x<=(*i1).y))||                              (((*i2).y>=(*i1).x)&&((*i2).y<=(*i1).y)))
    {
        printf("YES");
    }//checking overlapping
    else
    {
        printf("NO");
    }
    return 0;
}