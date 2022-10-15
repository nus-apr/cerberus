/*numPass=6, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 3", ExpOutput:"Acute Triangle", Output:"Acute Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 7", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 5", ExpOutput:"Obtuse Triangle", Output:"Obtuse Triangle"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 2 3", ExpOutput:"Invalid Triangle", Output:"Invalid TriangleObtuse Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"3 6 2", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"12 13 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
*/
#include<stdio.h>

int main(){
    int a;
    int b;
    int c;
    int max;
    scanf("%d%d%d",&a,&b,&c);
    if (a <= b){
        if(b >= c){
         max =b;
    } else {
         max=c;
    } } else {
        if (a <= c) {
         max=a;
        } else {
         max=c;
        }
    } 
    if ((a+b+c-(2*max))<=0) {
        printf("Invalid Triangle");
    }
    if ((a+b+c-(2*max))>=0) {
        if ((a*a)+(b*b)+(c*c)==(2*max*max)) {
            printf("Right Triangle");
        } else
        if((a*a)+(b*b)+(c*c)>=(2*max*max)) {
            printf("Acute Triangle");
        } else
        if((a*a)+(b*b)+(c*c)<=(2*max*max)) {
            printf("Obtuse Triangle");
        }
    }

    return 0;
}