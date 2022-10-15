/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"1 2 3 4 5 6 
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
3 2 4
5
9 2 1 4 6", ExpOutput:"1 2 3 4 6 9 
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 2 3 5 6
6
-6 -4 -2 -1 2 4
", ExpOutput:"-6 -4 -2 -1 1 2 3 4 5 6 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1
1
1
1
", ExpOutput:"1 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1
1
4
3 5 6 7
", ExpOutput:"1 3 5 6 7 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
9 2 1
3
1 2 9
", ExpOutput:"1 2 9 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
28 49 23 29 02 69 34
8
23 49 12 93 34 21 43 54", ExpOutput:"2 12 21 23 28 29 34 43 49 54 69 93 
", Output:""
*/
#include <stdio.h>
#include <stdlib.h>
struct set{
    int n;
    int* elements;
};
void read_to_struct(struct set* a)
{
    scanf("%d",&(a->n));
    int b=a->n;
    (a->elements)=(int*)malloc(sizeof(int)*b);
    for(int i=0;i<b;i++)
    {
        scanf("%d",(a->elements)+i);
    }
}
void union_set(struct set* a,struct set* b)
{
    int n1=a->n,n2=b->n;
    
}
int main() {
    struct set set1,set2;
    read_to_struct(&set1);
    read_to_struct(&set2);
    union_set(&set1,&set2);
    return 0;
}