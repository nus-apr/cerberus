/*numPass=9, numTotal=9
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
Verdict:ACCEPTED, Visibility:0, Input:"-1 -5
-6 9", ExpOutput:"YES
", Output:"YES"
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

struct point{
    int x;
    int y;
};
int main() {
    struct point* ptr;
    ptr=(struct point*)malloc(2*sizeof(struct point));
    scanf("%d %d\n",&ptr[0].x,&ptr[0].y);
    scanf("%d %d",&ptr[1].x,&ptr[1].y);
    if((ptr[0].x)>(ptr[1].x)&&(ptr[0].x)<(ptr[1].y))
    {
    printf("YES");
    return 0;
    }
    if((ptr[0].y)>(ptr[1].y)&&(ptr[0].x)<(ptr[1].x)){
      printf("YES"); 
      return 0;
    }
    if(ptr[0].x==ptr[1].x||ptr[0].x==ptr[1].y||ptr[0].y==ptr[1].x||ptr[0].y==ptr[1].y){
        printf("YES");
    return 0; 
    }
    
    else {
    printf("NO");
    }
    return 0;
}