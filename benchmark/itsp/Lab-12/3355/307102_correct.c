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
struct index{
    int x;
    int y;
};
struct interval{
    struct index left;
    struct index right;
};
struct interval pt;
int main() {
    int x,y;
    scanf("%d%d%d%d",&pt.left.x,&pt.left.y,&pt.right.x,&pt.right.y);
    if(pt.right.x>=pt.left.x && pt.right.x<=pt.left.y){
        printf("YES");
    } 
    else if(pt.right.y>=pt.left.x &&pt.right.y<=pt.left.y){
        printf("YES");
    }
    else if(pt.left.x>=pt.right.x && pt.left.x<=pt.right.y){
        printf("YES");
    }
    else if(pt.left.y>=pt.right.x && pt.left.y<=pt.right.y){
        printf("YES");
    }
    else printf("NO");
    return 0;
}