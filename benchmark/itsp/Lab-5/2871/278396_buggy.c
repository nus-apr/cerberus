/*numPass=2, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 4 5", ExpOutput:"1111
1  1
1  1
1  1
1111
", Output:"1  1
1  1
1  1
1  1
1  1
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5 6", ExpOutput:"22222
2   2
2   2
2   2
2   2
22222
", Output:"2   2
2   2
2   2
2   2
2   2
2   2
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9 6 7", ExpOutput:"999999
9    9
9    9
9    9
9    9
9    9
999999
", Output:"9    9
9    9
9    9
9    9
9    9
9    9
9    9
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 4 5", ExpOutput:"3333
3  3
3  3
3  3
3333
", Output:"3  3
3  3
3  3
3  3
3  3
"
Verdict:ACCEPTED, Visibility:1, Input:"2 2 2", ExpOutput:"22
22
", Output:"22
22
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 3", ExpOutput:"333
3 3
333
", Output:"3 3
3 3
3 3
"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1", ExpOutput:"1
", Output:"1"
*/
#include<stdio.h>

int main()
{
    int N;
    int w;
    int h;
    scanf("%d",&N);
    scanf("%d",&w);
    scanf("%d",&h);
    int a;
    int b;
    for(b=1;b<=h;b++)
    {
        for(a=1;a<=w;a++)
        {
            if(a==1)
            {
                printf("%d",N);
            }
            else if(a==w)
            {
                printf("%d",N);
                printf("\n");
            }
            else
            {
                printf(" ");
            }
        }
    }
    return 0;
}