/*numPass=5, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 6", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 10
-1 3", ExpOutput:"NO
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10 20
20 50", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"0 0
-1 0", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"-1 -5
-6 9", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 1
1 10", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"7 9
2 3", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 10
5 7", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"8 10
5 7", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>
#include <stdlib.h>

int main() {
    int i;
    struct point { int leftindex; int rightindex;};
    struct point* pts;
    pts=(struct point*)malloc(2*sizeof(struct point));
    for(i=0;i<2;i++){
        scanf("%d %d\n", &((*pts).leftindex),&((*pts).rightindex));
    }
    if((pts[0]).leftindex<=(pts[1]).rightindex)
    {
        printf("YES");
    }
    else if((pts[1]).leftindex>=(pts[0]).rightindex)
    {
        printf("YES");
    }
    else {printf("NO");}
    
    return 0;
}