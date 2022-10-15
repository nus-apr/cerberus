/*numPass=4, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 10
-1 6", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 3", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10 20
20 50", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"0 0
-1 0", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -5
-6 9", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 1
1 10", ExpOutput:"YES
", Output:"NO"
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
struct set
{
    int start;
    int end;
};
struct set input(int i,int j)
{
    struct set temp;
    temp.start=i;temp.start=j;
    return temp;
}
int main() {
    struct set set1;
    struct set set2;
    int start1,end1,start2,end2;
    scanf("%d %d",&start1,&end1);
    scanf("%d %d",&start2,&end2);
    set1=input(start1,end1);
    set2=input(start2,end2);
    if(((set1.start)<=(set2.start)&&(set2.start<=set1.end))||((set2.start)<=(set1.start)&&(set1.start<=set2.end)))
    printf("YES");
    else
    printf("NO");
    return 0;
}