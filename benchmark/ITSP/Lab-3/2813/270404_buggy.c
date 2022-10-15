/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 0 1", ExpOutput:"(0.000,0.000)
", Output:"inf"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:"inf"
Verdict:WRONG_ANSWER, Visibility:1, Input:"100 100 -1 -101", ExpOutput:"(-2.010,102.010)
", Output:"inf"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1000 000 1 -1", ExpOutput:"(1.000,0.000)
", Output:"inf"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -2 -3 -4", ExpOutput:"(3.000,-8.000)
", Output:"inf"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 0 000 0000", ExpOutput:"INF
", Output:"inf"
*/
#include<stdio.h>

int main(){
    float a1,b1,a2,b2,x,y,l,k;
    scanf("% %f %f %f",&a1,&b1,&a2,&b2);//input function 
      l=b1/a1;//slope line 1
      k=b2/a2;//slope line 2
    if(l==k)//equating slopes
        {printf("inf");}
    else
        {printf("(%.3f,%.3f)", x==a1*a2*(b2-b1)/(a1*b2-a2*b1),
         y==(a1-a2)*(b1*b2)/(a1*b2-a2*b1));}
	return 0;
}