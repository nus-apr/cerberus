/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangle is 13"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangle is 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangle is 7"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangle is 22"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangle is 50"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangle is 3"
*/
#include<stdio.h>

int main()
{
    int n,a,b,c,x=0;// x is the no. of triangles formed.a,b,c are sides of                      triangle.n is the input value.
    scanf("%d",&n);
    for(a=1;a<=n;a++)
    {
        for(b=a;b<=n;b++)
        {
            for(c=b;c<=n;c++)
            {
                if((a+b)>c&&(a+c)>b&&(b+c)>a)
                {
                    x++;
                }
            }
        }
    }
    printf("Number of possible triangle is %d",x);
    return 0;
}