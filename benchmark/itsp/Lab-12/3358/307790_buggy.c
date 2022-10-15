/*numPass=1, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:""
*/
#include <stdio.h>
#include <stdlib.h>
struct set {//define the structure 'set'
    int num;
    int *arr;
};

struct set set1,set2;
//set1=(struct set *)malloc(sizeof(struct set));
//set2=(struct set *)malloc(sizeof(struct set));

void read(struct set set1) {
    int t,i;
    scanf("%d",&t);
    (set1).num=t;
    set1.arr=(int *)malloc(t*sizeof (int));
    for (i=0;i<t;i++) {
        scanf("%d",(set1.arr)+i);
    }
   // return set1;
}


int main () {
    read(set1);
    
    printf("%d",(set1.arr)[2]);
    return 0;
}