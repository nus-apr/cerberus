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

struct range {
    int s;
    int e;
};

int chk (struct range r1, struct range r2) {
    int flag=0;
    if (r1.s<=r2.e && r1.s>=r2.s) {flag++;}
    if (r2.s<=r1.e && r2.s>=r1.s) {flag++;}
    if (r1.e<=r2.e && r1.e>=r2.s) {flag++;}
    if (r2.e<=r1.e && r2.e>=r1.s) {flag++;}
    return flag;
}

int main() {
    struct range r1;
    struct range r2;
    scanf("%d",&r1.s);
    scanf("%d",&r1.e);
    scanf("%d",&r2.s);
    scanf("%d",&r2.e);
    if (chk(r1,r2)) {printf("YES");}
    else {printf("NO");}
    return 0;
}