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
#include <stdlib.h>
struct point{
    int x;       // For the x coordinate of the point
    int y;       // For the y coordinate of the point
};
typedef struct point pt;   //This will act as an alias for struct point
struct rect{
    pt lefttop;
    pt rightbot;
};
typedef struct rect rt;    // This will act as an alias for struct rect 
void read_point(rt* rectangle,int i);  // All the points reading

int overlapping(rt* rectangle); // Confirns whether it is overlapping                                                   or not
int liesbetween(rt* rectangle,int i);

int main() {
    int i;
    rt* rectangle;
    rectangle=(rt*)malloc(2*sizeof(rt));
    for(i=0;i<2;i++)
    {
        read_point(rectangle,i);
    }
    if(overlapping(rectangle))
    {
        printf("YES");
    }
    else
    {
        printf("NO");
    }
    return 0;
}

void read_point(rt* rectangle,int i)
{
    int j;
    for(j=0;j<2;j++)
    {
        if(j==0)
        {
            scanf("%d",&(rectangle[i].lefttop.x));
            scanf("%d",&(rectangle[i].lefttop.y));
        }
        else
        {
            scanf("%d",&(rectangle[i].rightbot.x));
            scanf("%d",&(rectangle[i].rightbot.y));
        }
}
}
int overlapping(rt*rectangle)
{
    int index;
    int i=0;
    if((rectangle[i].lefttop.x)>(rectangle[i+1].lefttop.x))
    {
        rt rect1;
        rect1=rectangle[i];
        rectangle[i]=rectangle[i+1];
        rectangle[i+1]=rect1;
    }
    for(i=0;i<2;i++)
    {
    if(liesbetween(rectangle,i))
    {
        return 1;
    }
    }
    return 0;
}

int liesbetween(rt* rectangle,int i)
{
    int j=0,count=0;
    if(i==0)
    {
        if((rectangle[j+1].lefttop.x)<=(rectangle[j].rightbot.x)&& (rectangle[j].lefttop.y)>=(rectangle[j+1].lefttop.y)&&(rectangle[j].rightbot.y)<=(rectangle[j+1].lefttop.y))
        {
            return 1;
        }
        else 
        {
            count ++;
        }
    }
    else
    {
        if((rectangle[j+1].rightbot.x)<=(rectangle[j].rightbot.x)&& (rectangle[j].lefttop.y)>=(rectangle[j+1].rightbot.y)&&(rectangle[j].rightbot.y)<=(rectangle[j+1].rightbot.y))
        {
            return 1;
        }
    }
    if(count==1)
    {
        return 0;
    }
}