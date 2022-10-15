/*numPass=2, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 10"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 6"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 15"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 28"
Verdict:ACCEPTED, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 3"
*/
#include<stdio.h>

int main()
{
    int n;
    int count=0;
    scanf("%d",&n);
    for(int i=1;i<=n;i++)
    {
        for(int j=1;j<=i;j++)
        {
            for(int k=1;k<=j;k++)
            {
                if((j+k)>i)
                {
                    count=count+1;
                }
                else
                {
                    break;
                }
            }
        }
    }
    printf("Number of possible triangles is %d",count);
    return 0;
}