/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:""
*/
#include<stdio.h>

int main()
{
    int n,c=0,i,j,k,d=0;
    scanf("%d",&n);
    for(i=n;i>=1;i++)
    {
        for(j=i;j>=1;j--)
        {
            for(k=j;k>=1;k--)
            {
                if(j+k>i)
                c++;
                else
                d++;
            }
        }
    }
    printf("Number of possible triangles is %d",c);
    return 0;
}