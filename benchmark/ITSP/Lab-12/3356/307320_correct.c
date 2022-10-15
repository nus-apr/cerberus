/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"1 10 4 1
2 9 3 2", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"3 7 7 3
4 5 5 4", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"0 5 5 0
3 7 5 6", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 6 0
3 3 5 0", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 6 0
7 3 10 0", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"-5 -5 -2 -10
5 5 10 2", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"0 0 5 -5
1 -1 4 -4", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>

int main() {
    typedef struct point{
        int x;
        int y;
    }Point;
    struct rect{
        Point leftbot;
        Point lefttop;
        Point rightbot;
        Point righttop;
    };
    struct rect r,s;
    scanf("%d %d",&r.lefttop.x,&r.lefttop.y);
    scanf("%d %d",&r.rightbot.x,&r.rightbot.y);
    scanf("%d %d",&s.lefttop.x,&s.lefttop.y);
    scanf("%d %d",&s.rightbot.x,&s.rightbot.y);
    r.leftbot.y=r.rightbot.y;
    r.leftbot.x=r.lefttop.x;
    r.righttop.x=r.rightbot.x;
    r.righttop.y=r.lefttop.y;
    s.leftbot.y=s.rightbot.y;
    s.leftbot.x=s.lefttop.x;
    s.righttop.x=s.rightbot.x;
    s.righttop.y=s.lefttop.y;
    int a=r.rightbot.x;
    int b=r.rightbot.y;
    int c=r.lefttop.x;
    int d=r.lefttop.y;
    int e=s.rightbot.x;
    int f=s.rightbot.y;
    int g=s.lefttop.x;
    int h=s.lefttop.y;
    int i=0,j=0;
    if(((c<=g&&g<=a)&&(b<=h&&h<=d))||((c<=e&&e<=a)&&(b<=f&&f<=d))){
        i=1;
    }
    if(((g<=c&&c<=e)&&(f<=d&&d<=h))||((g<=a&&a<=e)&&(f<=b&&b<=h))){
        j=1;
    }
    if(i==1||j==1){
        printf("YES");
    }
    else printf("NO");
    return 0;
}