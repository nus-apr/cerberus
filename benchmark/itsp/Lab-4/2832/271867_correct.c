/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 3", ExpOutput:"Acute Triangle", Output:"Acute Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 7", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 5", ExpOutput:"Obtuse Triangle", Output:"Obtuse Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"1 2 3", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"3 6 2", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"12 13 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
*/
#include<stdio.h>

int main(){
    int a,b,c;
    scanf("%d %d %d",&a,&b,&c);
    if(a>=b){
        int x;
        x=a;
        a=b;
        b=x;
    }
    if(c<=b){
        int y;
        y=b;
        b=c;
        c=y;
    }
    if(a+b<=c){
        printf("Invalid Triangle");
    }
    else{
        if(a*a+b*b==c*c){
            printf("Right Triangle");
        }
        else if(a*a+b*b>c*c){
            printf("Acute Triangle");
        }
        else{
            printf("Obtuse Triangle");
        }
    }


    // Fill this area with your code.
    return 0;
}