/*numPass=6, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 4 3", ExpOutput:"Acute Triangle", Output:"Obtuse Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 7", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 5", ExpOutput:"Obtuse Triangle", Output:"Obtuse Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"1 2 3", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"3 6 2", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"12 13 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
*/
#include<stdio.h>


int main()
{
int a;
int b;
int c;
scanf("%d %d %d",&a,&b,&c);
if((a+b>c)&&(b+c>a)&&(a+c>b)){
if(((a*a)==(b*b)+(c*c))||((b*b)==(a*a)+(c*c))||((c*c)==(a*a)+(b*b))) {
    printf("Right Triangle");
}
else if(((a*a)<(b*b)+(c*c))||((b*b)<(c*c)+(a*a))||((c*c)<(b*b)+(a*a))) {
    printf("Obtuse Triangle");
} 
else if(((a*a)>(b*b)+(c*c))||((b*b)>(c*c)+(a*a))||((c*c)>(b*b)+(a*a))) {
    printf("Acute Triangle");
}}
else{
    printf("Invalid Triangle");
}
    return 0;
}