/*numPass=3, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 0 4
1 1 3", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 0 4
10 10 3", ExpOutput:"NO
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"-1 -1 5
6 6 5", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"-1 -1 1
5 -1 1", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"2 2 2
2 2 1", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 0 3
-4 0 3", ExpOutput:"NO
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 0 1
3 0 3", ExpOutput:"YES
", Output:"NO"
*/
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
struct point{
    int x;
    int y;
    int r;
};

float dis(int x1,int y1,int x2,int y2)
{
  float a;
  a=sqrt((x1-x2)^2+(y1-y2)^2);
  return a;
}
 
/*struct point_make_point(int x, int y,int r) 
{
    structpoint temp;
    temp.x= x;
    temp.y= y;
    temp.r=r
    return temp;
    
};  */
  
//scanf("%d%d%d",&(pt1.x),&(pt1.y),&r1);    
//scanf("%d%d%d",&(pt2.x),&(pt2.y),&r2);      
    
int main() 
{
    
struct point pt1,pt2; 
float distance;


scanf("%d%d%d",&(pt1.x),&(pt1.y),&(pt1.r));    
scanf("%d%d%d",&(pt2.x),&(pt2.y),&(pt2.r));      
    
//printf("%d/n",(pt1.x));    
    
distance=dis((pt1.x),(pt1.y),(pt2.x),(pt2.y));

  if(((pt1.r)+(pt2.r))>(distance))
      printf("YES");
  else
      printf("NO");
    

return 0;
}