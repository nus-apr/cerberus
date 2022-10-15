/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:"2 3 4 5 6 2 3 4 5 6 2 3 4 5 6 2 3 4 5 6 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:"4 6 8 4 6 8 4 6 8 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:"3 6 7 3 6 7 3 6 7 3 6 7 3 6 7 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:"3 6 7 3 6 7 3 6 7 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:"1 4 5 1 4 5 1 4 5 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1 4 6 10 12 1 4 6 10 12 1 4 6 10 12 1 4 6 10 12 1 4 6 10 12 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:"1 4 6 10 12 1 4 6 10 12 1 4 6 10 12 "
*/
#include <stdio.h>
#include <stdlib.h>

struct set{
    int a;int* b;
};
struct set intersection()
{
    struct set pt;
    int n,i;
    scanf("%d\n",&n);
    pt.a=n;
    pt.b=(int*)malloc(n*sizeof(int));
    for(i=0;i<n;i++){
        scanf("%d ",&(pt.b[i]));
    }
    return pt;
}

int main(){
    struct set s1;
    struct set s2;
    s1=intersection();
    s2=intersection();
    int i,j;
    for(i=0;i<s1.a;i++){
        for(j=0;j<s2.a;j++){
            if((s1.b[i])=(s2.b[j])){
                printf("%d ",s1.b[i]);
            }
        }
    }
}