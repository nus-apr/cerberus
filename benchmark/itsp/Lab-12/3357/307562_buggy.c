/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 0 4
1 1 3", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 0 4
10 10 3", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"-1 -1 5
6 6 5", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -1 1
5 -1 1", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"2 2 2
2 2 1", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 0 3
-4 0 3", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 0 1
3 0 3", ExpOutput:"YES
", Output:""
*/
#include<stdio.h>
#include<stdlib.h>
#include<math.h>
struct Circle{
    int x;
    int y;
    int r;
};
typedef struct Circle* circle;
int main()
{
    circle c1,c2;
    scanf("%d %d %d\n",&c1->x,&c1->y,&c1->r);
    scanf("%d %d %d\n",&c2->x,&c2->y,&c2->r);
    if((pow((c1->x-c2->x),2)+pow((c1->y-c2->y),2))<=pow((c1->r+c2->r),2))
        printf("YES");
    else 
        printf("NO");
    return 0;
}