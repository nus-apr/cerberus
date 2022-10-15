/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2-32"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"201510505101520"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4-14"
Verdict:WRONG_ANSWER, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"161161-4161116"
*/
#include <stdio.h>
int x;
void f(int n)
{
    static int c=0;
    c++;
    printf("%d",n);
    if(c==(2*x+1))
    {return;}
    if(c<=x)
    {
        f(n-5);
    }
    else
    {
        f(n+5);
    }
}
int main()
{   
    int N;
    scanf("%d",&N);
    int a;
    int b;
    a=N/5;
    b=N%5;
    if(b>0)
    {
        x=a+1;
    }
    else
    x=a;
    f(N);
	return 0;
}