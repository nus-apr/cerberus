/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"1 0 0 1", ExpOutput:"(0.000,0.000)
", Output:"(0.000,0.000)"
Verdict:ACCEPTED, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:"INF"
Verdict:ACCEPTED, Visibility:1, Input:"100 100 -1 -101", ExpOutput:"(-2.010,102.010)
", Output:"(-2.010,102.010)"
Verdict:ACCEPTED, Visibility:0, Input:"1000 000 1 -1", ExpOutput:"(1.000,0.000)
", Output:"(1.000,0.000)"
Verdict:ACCEPTED, Visibility:0, Input:"-1 -2 -3 -4", ExpOutput:"(3.000,-8.000)
", Output:"(3.000,-8.000)"
Verdict:ACCEPTED, Visibility:0, Input:"0 0 000 0000", ExpOutput:"INF
", Output:"INF"
*/
#include<stdio.h>

int main(){
    float a,b,c,d;
    scanf("%f %f %f %f", &a,&b,&c,&d);
    float X=(b-d)*(a*c)/(b*c-a*d);
    float Y=(a-c)*(b*d)/(a*d-b*c);
    float E=a*d-b*c;
    if (E==0)
    {
        printf("INF");
    }
    else
    {
    printf("(%.3f,%.3f)",X,Y);
    }
    
	
	return 0;
}