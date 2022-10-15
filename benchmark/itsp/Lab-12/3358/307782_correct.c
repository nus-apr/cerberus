/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:"2 3 4 "
Verdict:ACCEPTED, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:"6 "
Verdict:ACCEPTED, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:"6 "
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:"1 4 5 "
Verdict:ACCEPTED, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1 4 12 "
Verdict:ACCEPTED, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:"12 "
*/
#include <stdio.h>
#include <stdlib.h>
int x,y,a;
struct point 
{
    int x;int y;
};
//struct rect
//{
struct point* pts;
struct point* atp;
    
//};
struct rect *pr;
void compare(struct point*pts,struct point*atp,int x,int y);
int main()
{
    
    scanf("%d",&x); 
    int i;
    pts=(struct point*)(malloc(x*sizeof(struct point)));
    for(i=0;i<x;i++)
    {   scanf("%d",&a);
        pts[i].x=a;
      //  printf("%d",pts[i]);
    }
    scanf("%d",&y); 
    int j;
    atp=(struct point*)(malloc(y*sizeof(struct point)));
    for(j=0;j<y;j++)
    {   scanf("%d",&a);
        atp[j].x=a;
       // scanf("%d ",atp[j]);
    }
    
    compare(pts,atp,x,y);
}
void compare(struct point*pts,struct point*atp,int x,int y)
{   int i,j;
    for(i=0;i<=x;i++)
    {
        for(j=0;j<=y;j++)
        {
            if(pts[i].x==atp[j].x)
            {
                printf("%d ",pts[i].x);
            }
        }
    }
}
