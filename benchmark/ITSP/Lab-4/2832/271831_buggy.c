/*numPass=6, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"Right Triangle", Output:"Right Triangle
"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 3", ExpOutput:"Acute Triangle", Output:"Acute Triangle
"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 7", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle
"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 5", ExpOutput:"Obtuse Triangle", Output:"Obtuse Triangle
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 2 3", ExpOutput:"Invalid Triangle", Output:"Obtuse Triangle
"
Verdict:ACCEPTED, Visibility:0, Input:"3 6 2", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle
"
Verdict:ACCEPTED, Visibility:0, Input:"12 13 5", ExpOutput:"Right Triangle", Output:"Right Triangle
"
*/
#include<stdio.h>
#include<math.h>
int main()
{
    int a,b,c;
    scanf("%d %d%d\n",&a,&b,&c);
    float cA, cB, cC;
    cA=((b*b+c*c-a*a)*1.0)/(2*b*c);
    cB=((a*a+c*c-b*b)*1.0)/(2*a*c);
    cC=((b*b+a*a-c*c)*1.0)/(2*b*a);
    if((c*sqrt(1+cB)<=b)||(a*sqrt(1+cC)<=c)||(b*sqrt(1+cA)<=a))
    {
        if(cA<0.0||cB<0.0||cC<0.0)
        {
            printf("Obtuse Triangle\n");
        }    
        else
        {
            if(cA==0.0||cB==0.0||cC==0.0)
            {
                printf("Right Triangle\n");
            }
            else
            {
                if(cA>0.0&&cB>0.0&&cC>0.0)
                {
                    printf("Acute Triangle\n");
                }    
            }
        }
    }
    else
    {
        printf("Invalid Triangle\n");
    }
    return 0;
}