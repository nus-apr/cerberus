/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 13"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 7"
Verdict:ACCEPTED, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 22"
Verdict:ACCEPTED, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 50"
Verdict:ACCEPTED, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 3"
*/
#include<stdio.h>

int main()
{
    int N;
    int a,b,c;//N,a,b,c are declared as int variables
    a=1;
    b=1;
    c=1;  //a,b,c are assigned as 1
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
                if(a<b+c&&b<a+c&&c<a+b&&(a>=b&&b>=c))
                {
                    count+=1;           // increment of count
                }
                c+=1;                   //increment of c
            }
            b+=1;                       //increment of b
        }
        a+=1;                           //increment of a
    }
    printf("Number of possible triangles is %d", count);
    return 0;
}