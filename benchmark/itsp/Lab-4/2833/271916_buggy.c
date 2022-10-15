/*numPass=3, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 11"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 7"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 17"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 31"
Verdict:ACCEPTED, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 3"
*/
#include<stdio.h>

int main()
{
    int n,count=0,a,b,c;
    scanf("%d",&n);
    for(a=1;a<=n;a++)
    {
        for(b=1;b<=n;b++)
        {
            for(c=1;c<=n;c++)
            {
               if((a+b)>c && (a+c)>b && (b+c)>a)
               {
                   count++;
               }
            }
        }
    }
    count=(((count-n)/n)+n);
    printf("Number of possible triangles is %d",count);
    return 0;
}