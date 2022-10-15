/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"1 5 7 2", ExpOutput:"The second largest number is 5", Output:"The second largest number is 5 
"
Verdict:ACCEPTED, Visibility:1, Input:"8 6 4 2", ExpOutput:"The second largest number is 6", Output:"The second largest number is 6 
"
Verdict:ACCEPTED, Visibility:0, Input:"1 10 15 3", ExpOutput:"The second largest number is 10", Output:"The second largest number is 10 
"
Verdict:ACCEPTED, Visibility:0, Input:"1 3 3 2 ", ExpOutput:"The second largest number is 3", Output:"The second largest number is 3 
"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1 2", ExpOutput:"The second largest number is 1", Output:"The second largest number is 1 
"
*/
#include<stdio.h>

int main()
{   int a,b,c,d;
    scanf("%d%d%d%d",&a,&b,&c,&d);
    if (a>=b && a>=c && a>=d){ /*a>b,a>c and a>d */
        if (b>=c && b>=d)
            printf("The second largest number is %d \n",b);
        else if (c>=b && c>=d) 
            printf("The second largest number is %d \n",c);
        else if (d>=b && d>=c)
            printf("The second largest number is %d \n",d);
    }
    else if (b>=a && b>=c && b>=d){ /*b>a,b>c and b>d */
         if (a>=c && a>=d)
           printf("The second largest number is %d \n",a);
        else if (c>=a && c>=d)
           printf("The second largest number is %d \n",c);
        else if (d>=c && d>=a)
           printf("The second largest number is %d \n",d);
    }
    else if (c>=a && c>=b && c>=d){ /*c>a,c>b and c>d*/
         if (d>=a && d>=b)
           printf("The second largest number is %d \n",d);
        else if (a>=b && a>=d)
           printf("The second largest number is %d \n",a);
        else if (b>=a && b>=d)
           printf("The second largest number is %d \n",b);
    }
    else if (d>=a && d>=b && d>=c){ /*d>a,d>b and d>c */
         if (c>=a && c>=b)
           printf("The second largest number is %d \n",c);
        else if (a>=c && a>=b)
           printf("The second largest number is %d \n",a);
        else if (b>=a && b>=c)
           printf("The second largest number is %d \n",b);
            }
    // Fill this area with your code.
    return 0;
}