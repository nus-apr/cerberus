/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 10 4 1
2 9 3 2", ExpOutput:"YES
", Output:"1 10 4 1
2 9 3 2"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 7 7 3
4 5 5 4", ExpOutput:"YES
", Output:"3 7 7 3
4 5 5 4"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 5 5 0
3 7 5 6", ExpOutput:"NO
", Output:"0 5 5 0
3 7 5 6"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 6 0
3 3 5 0", ExpOutput:"YES
", Output:"3 3 6 0
3 3 5 0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 6 0
7 3 10 0", ExpOutput:"NO
", Output:"3 3 6 0
7 3 10 0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-5 -5 -2 -10
5 5 10 2", ExpOutput:"NO
", Output:"-5 -5 -2 -10
5 5 10 2"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 0 5 -5
1 -1 4 -4", ExpOutput:"YES
", Output:"0 0 5 -5
1 -1 4 -4"
*/
#include <stdio.h>
struct cord{
    int x;
    int y;
};
struct rect{
    struct cord leftop;
    struct cord rightbot;
};
int main() {
    struct rect r1;
    struct rect r2;
    scanf("%d %d %d %d\n",&(r1.leftop.x),&(r1.leftop.y),&(r2.rightbot.x),&(r2.rightbot.y));
    struct rect s1;
    struct rect s2;
    scanf("%d %d %d %d",&(s1.leftop.x),&(s1.leftop.y),&(s2.rightbot.x),&(s2.rightbot.y));
    printf("%d %d %d %d\n",(r1.leftop.x),(r1.leftop.y),(r2.rightbot.x),(r2.rightbot.y));
    printf("%d %d %d %d",(s1.leftop.x),(s1.leftop.y),(s2.rightbot.x),(s2.rightbot.y));
    return 0;
}