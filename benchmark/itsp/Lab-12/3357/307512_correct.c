/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"0 0 4
1 1 3", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"0 0 4
10 10 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"-1 -1 5
6 6 5", ExpOutput:"YES
", Output:"YES"
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
#include <stdio.h>
#include <stdlib.h>
struct cir{
    int x,y,r;
};
typedef struct cir Cir;
void input(struct cir *p){
    scanf("%d %d %d",&(p->x),&(p->y),&(p->r));
}
int main(){
    Cir c1,c2;
    input(&c1);
    input(&c2);
    int d=(c1.x-c2.x)*(c1.x-c2.x)+(c1.y-c2.y)*(c1.y-c2.y);
    (d<=((c1.r+c2.r)*(c1.r+c2.r)))?printf("YES"):printf("NO");
}