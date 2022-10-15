/*numPass=5, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"1 10 4 1
2 9 3 2", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"3 7 7 3
4 5 5 4", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 5 5 0
3 7 5 6", ExpOutput:"NO
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 6 0
3 3 5 0", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 6 0
7 3 10 0", ExpOutput:"NO
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"-5 -5 -2 -10
5 5 10 2", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"0 0 5 -5
1 -1 4 -4", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>
struct point{
    float x; float y;
};
typedef struct point pt;
struct rect{
    pt A; pt B;
};
typedef struct rect rect;
float distsqr(pt A,pt B){
    float t;
    t= (A.x-B.x)*(A.x-B.x)+(A.y-B.y)*(A.y-B.y);
    return t;
}
float max(float a,float b){
    if(a>b) return a;
    else return b;
}
float min(float a,float b){
    if(a<b) return a;
    else return b;
}
int main() {
    rect X,Y;
    scanf("%f%f%f%f",&X.A.x,&X.A.y,&X.B.x,&X.B.y);
    scanf("%f%f%f%f",&Y.A.x,&Y.A.y,&Y.B.x,&Y.B.y);
    pt mid1,mid2;
    mid1.x= (X.A.x+X.B.x)/2.0;
    mid1.y= (X.A.y+X.B.y)/2.0;
    mid2.x= (Y.A.x+Y.B.x)/2.0;
    mid2.y= (Y.A.y+Y.B.y)/2.0;
    float l1=max(X.A.x,X.B.x)-min(X.A.x,X.B.x);
    float l2=max(Y.A.x,Y.B.x)-min(Y.A.x,Y.B.x);
    float b1=max(X.A.y,X.B.y)-min(X.A.y,X.B.y);
    float b2=max(Y.A.y,Y.B.y)-min(Y.A.y,Y.B.y);
    float d1=((l1+l2)*(l1+l2))/4.0;
    float d2=((b1+b2)*(b1+b2))/4.0;
    float z=distsqr(mid1,mid2);
    if(z>=d1+d2) printf("NO");
    else printf("YES");
    return 0;
}