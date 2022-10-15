/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2 -3"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"20 15 10 5 0 10 15 20"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4 -1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"16 11 6 1 -4 6 11 16"
*/
#include <stdio.h>

void pattern(int n);

int main()
{
    int n;
    scanf("%d",&n);
    printf("%d",n);
    pattern(n);
	return 0;
}

void pattern(int n)
{
    n-=5;
    printf(" %d",n);
    if(n<=0)
    {
        return;
    }
    pattern(n);
    n+=5;
    printf(" %d",n);
}