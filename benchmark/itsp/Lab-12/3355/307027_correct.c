/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 6", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"10 20
20 50", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"0 0
-1 0", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"-1 -5
-6 9", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"0 1
1 10", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"7 9
2 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"1 10
5 7", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"8 10
5 7", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>

struct interval{
    int left;
    int right;
};

struct interval input(){
    struct interval i;
    scanf("%d%d",&i.left,&i.right);
    return i;
}

void check_overlap(struct interval i1, struct interval i2){
    if(i1.left<=i2.right&&i1.left>=i2.left)
        printf("YES");
    else
    {
        if(i1.right>=i2.left&&i1.right<=i2.right)
            printf("YES");
            
    }
        printf("NO");
}

void checkoverlap(struct interval i1, struct interval i2){
    if((i1.left<i2.left&&i1.right<i2.left)||(i2.left<i1.left&&i2.right<i1.left))
        printf("NO");
    else
        printf("YES");
}

int main() {
    struct interval i1,i2;
    i1=input();
    i2=input();
    checkoverlap(i1,i2);
    return 0;
}