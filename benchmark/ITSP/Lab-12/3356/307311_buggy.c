/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 10 4 1
2 9 3 2", ExpOutput:"YES
", Output:"11YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 7 7 3
4 5 5 4", ExpOutput:"YES
", Output:"11YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0 5 5 0
3 7 5 6", ExpOutput:"NO
", Output:"10YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 6 0
3 3 5 0", ExpOutput:"YES
", Output:"11YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 6 0
7 3 10 0", ExpOutput:"NO
", Output:"01YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-5 -5 -2 -10
5 5 10 2", ExpOutput:"NO
", Output:"00YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 0 5 -5
1 -1 4 -4", ExpOutput:"YES
", Output:"11YES"
*/
#include <stdio.h>
#include<stdlib.h>

int interval(int a1, int b1, int a2, int b2){
    int check=0;
    if(((a2<=b1)&&(a2>=a1))||((b2<=b1)&&(b2>=a1))||(((a1>=a2)&&(b1>=a2))&&(a1<=b2)&&(b1<=b2))){
        check=1;
    }
    return check;
}


struct point{
    int x;
    int y;
};

typedef struct point Point;

struct rect{
    struct point left_top;
    struct point right_bot;
};

typedef struct rect Rect;

int main() {
    Rect* r;
    int check1,check2;
    r=(Rect*)malloc(2*sizeof(Rect));
    int i;
    for(i=0;i<2;i++){
        scanf("%d%d",&(r[i]).left_top.x,&(r[i]).left_top.y);
        scanf("%d%d",&(r[i]).right_bot.x,&(r[i]).right_bot.y);
    }
    check1=interval((r[0]).left_top.x,(r[0]).right_bot.x,(r[1]).left_top.x,(r[1]).right_bot.x);
    check2=interval((r[0]).right_bot.y,(r[0]).left_top.y,(r[1]).right_bot.y,(r[1]).left_top.y);
    printf("%d%d",check1,check2);
    if((check1=1)&&(check2=1)){
        printf("YES");
    }
    else{
        printf("NO");
    }
    return 0;
}