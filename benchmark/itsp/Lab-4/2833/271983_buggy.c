/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 64"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 27"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 125"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 343"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 8"
*/
#include<stdio.h>

int main()
{
    int N;
    int a,b,c;
    a=1;
    b=1;
    c=1;
    int count=0;
    scanf("%d", &N);
    while(a<=N)
    { 
        b=1;
        while(b<=N)
        {
           c=1;
           while(c<=N)
            {
                if(a<b+c||b<a+c||c<a+b)
                {
                    count+=1;
                }
                c+=1;
            }
            b+=1;
        }
        a+=1;
    }
    printf("Number of possible triangles is %d", count);
    return 0;
}