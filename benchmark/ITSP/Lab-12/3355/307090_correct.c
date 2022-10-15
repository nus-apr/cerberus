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
struct interval{     //declaring structure with two subfields
    int leftindex;
    int rightindex;     
    
};

int check_overlap(struct interval i1,struct interval i2)
{   //returns 1 if intervals are overlapping otherwise 0
    if(i1.leftindex>=i2.leftindex&&i1.leftindex<=i2.rightindex)
    return 1;
    if(i2.leftindex>=i1.leftindex&&i2.leftindex<=i1.rightindex)
    return 1;
    return 0;
}
int main() {
struct interval* arri; //declaring a pointer to structure
arri=(struct interval*)malloc(2*sizeof(struct interval));
scanf("%d %d\n",&arri[0].leftindex,&arri[0].rightindex);
scanf("%d %d",&arri[1].leftindex,&arri[1].rightindex);
int c;
c=check_overlap(arri[0],arri[1]);
if(c==1)   //displaying the desired output
printf("YES");
else
printf("NO");
    return 0;
}