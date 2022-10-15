/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:"2 3 4 "
Verdict:ACCEPTED, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:"6 "
Verdict:ACCEPTED, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:"6 "
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:"1 4 5 "
Verdict:ACCEPTED, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1 4 12 "
Verdict:ACCEPTED, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:"12 "
*/
#include <stdio.h>
#include <stdlib.h>
struct set {//define the structure 'set'
    int num;
    int *arr;
};
void check_intersection (struct set *pt1,struct set *pt2) {
    int i,j,l1,l2;
    l1=pt1->num;
    l2=pt2->num;
    for (i=0;i<l1;i++) {
        for (j=0;j<l2;j++) {
            if ((pt1->arr)[i]==(pt2->arr)[j]) {
                printf("%d ",(pt1->arr)[i]);break;
            }    
        }
    }
}
int main () {
    int i;
    struct set set1;//read first set.
    scanf("%d",&(set1.num));
    set1.arr=(int *)malloc((set1.num)*sizeof(int));
    for (i=0;i<set1.num;i++) {
        scanf("%d",set1.arr+i);
    }
    struct set set2;//read second set.
    scanf("%d",&(set2.num));
    set2.arr=(int *)malloc((set2.num)*sizeof(int));
    for (i=0;i<set2.num;i++) {
        scanf("%d",set2.arr+i);
    }
    struct set *pt1=&set1;
    struct set *pt2=&set2;
    check_intersection(pt1,pt2);
    return 0;
}