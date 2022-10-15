/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 20"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 10"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 35"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 84"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 4"
*/
#include<stdio.h>

int main()
{
    int n,a=1,b=1,c=1,i;
    scanf("%d",&n);
    i=0;
    for(a=1;a<=n;a++)
    {
    for(b=1;b<=a;b++)
    {
    for(c=1;c<=b;c++)
    {
     if(a+b>c||b+c>a||c+a>b)
     {
        i++; 
     }
    }   
    }
    }
    printf("Number of possible triangles is %d",i);
    return 0;
}