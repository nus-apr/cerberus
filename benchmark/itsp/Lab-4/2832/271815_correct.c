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

int main()
{
    int a;
    int b;
    int c;   //Declaring variables
    scanf("%d %d %d",&a,&b,&c); //Taking input
    
    if(a+b<= c||b+c<= a||a+c<= b)  //Using if-else
        {
            printf("Invalid Triangle");
        }        //Checking if invalid triangle
    else if(a*a+b*b==c*c||b*b+c*c==a*a||a*a+c*c==b*b)
        {
            printf("Right Triangle");
        }           //Checking if right triangle

    else if((c>=a&&c>=b)&&(c*c>a*a+b*b)||(a>=b&&a>=c)&&(a*a>b*b     +c*c)||(b>=a&&b>=c)&&(b*b>a*a+c*c))
        {
            printf("Obtuse Triangle");
        }    //Checking if obtuse triangle
    else
        { 
            printf("Acute Triangle");
        }//if no above case satisfies then acute triangle
   
    return 0;
}