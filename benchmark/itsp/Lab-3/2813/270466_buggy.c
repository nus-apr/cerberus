/*numPass=5, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"1 0 0 1", ExpOutput:"(0.000,0.000)
", Output:"(0.000,0.000)"
Verdict:ACCEPTED, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:"INF
"
Verdict:ACCEPTED, Visibility:1, Input:"100 100 -1 -101", ExpOutput:"(-2.010,102.010)
", Output:"(-2.010,102.010)"
Verdict:ACCEPTED, Visibility:0, Input:"1000 000 1 -1", ExpOutput:"(1.000,0.000)
", Output:"(1.000,0.000)"
Verdict:ACCEPTED, Visibility:0, Input:"-1 -2 -3 -4", ExpOutput:"(3.000,-8.000)
", Output:"(3.000,-8.000)"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 0 000 0000", ExpOutput:"INF
", Output:"(-nan,-nan)"
*/
#include<stdio.h>

int main(){
float a1,a2,b1,b2;
scanf("%f %f %f %f",&a1,&b1,&a2,&b2);
float c=a1/b1;
float d=a2/b2;
float x=((b1-b2)*(a1*a2))/((b1*a2)-(b2*a1));
float y=((a1-a2)*(b1*b2))/((a1*b2)-(a2*b1));

if (c==d) {
    printf ("INF\n");
}
    else if (c!=d ) {
        if (x==0)
            x=0;
        if (y==0)
            y=0;
        
        printf ("(%.3f,%.3f)",x,y);
    }

return 0;
}