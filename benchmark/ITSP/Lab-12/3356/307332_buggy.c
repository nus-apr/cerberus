/*numPass=4, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 10 4 1
2 9 3 2", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"3 7 7 3
4 5 5 4", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"0 5 5 0
3 7 5 6", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 6 0
3 3 5 0", ExpOutput:"YES
", Output:"NO"
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
int main() {
    
int i,j,a[10],b[10],c[10];    

struct point 
{
	int x; int y;
};
    struct point* pts;
      pts = (struct point*) malloc(4 * sizeof(struct point));
   
    for(i=0;i<4;i++)
{
    scanf("%d %d",&(pts[i].x),&(pts[i].y));
}
 
   for(i=0;i<4;i=i+2)
   {
       a[i]=(pts[i].x-pts[i+1].x)/2;
       a[i+1]=(pts[i].y-pts[i].y)/2;
   }
   for(i=0;i<4;i=i+2)
   {
       b[i]=(pts[i].x+pts[i+1].x)/2;
       b[i+1]=(pts[i].y+pts[i+1].y)/2;
   }
    
    for(i=0;i<1;i=i+2)
    {
        c[i]=b[i]-b[i+2];
        c[i+1]=b[i+1]-b[i+3];
    }
    
    
    for(i=0;i<1;i++)
    {
        if((c[i]>(a[i]+a[i+2]))&&(c[i+1]>(a[i+1]+a[i+3])))
        printf("YES");
        else
        printf("NO");
        
    }
    return 0;
}