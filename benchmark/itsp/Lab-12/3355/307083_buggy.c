/*numPass=7, numTotal=9
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -5
-6 9", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"0 1
1 10", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"7 9
2 3", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 10
5 7", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"8 10
5 7", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>
struct interval{
        int left;
        int right;
    };

int main() {
    struct interval first;
    struct interval second;
    
    scanf("%d %d %d %d",&(first.left),&(first.right),&(second.left),&(second.right));
    
    if(first.left>second.left)
    {
        if(second.right>=first.left&&second.right<=first.right)
        printf("YES");
        else
        printf("NO");
    }
    
    if(first.left<second.left)
    {
        if(first.right>=second.left&&first.right<=second.right)
        printf("YES");
        else
        printf("NO");
    }
    
    if(first.left==second.left)
    printf("YES");
    
    
    return 0;
}