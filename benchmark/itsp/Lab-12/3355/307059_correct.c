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

typedef struct interval{
    int x;
    int y;
}range;

range *r1,*r2;
void check(){
   range *r3;    
    r3=(range*)malloc(sizeof(range));
    if(r1->x>r2->x){
     r3=r1;
     r1=r2;
     r2=r3;
    }
    
} 

int main() {
 
  
   r1=(range*)malloc(sizeof(range));
   r2=(range*)malloc(sizeof(range));
   scanf("%d%d%d%d",&(r1->x),&(r1->y),&(r2->x),&(r2->y));
    check();
    if((r1->y)>=(r2->x))
        printf("YES");
    else
        printf("NO");
    return 0;
}