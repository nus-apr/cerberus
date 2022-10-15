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
", Output:"6 6 6 "
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
", Output:"1 1 1 4 4 4 5 5 5 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1 1 1 1 1 4 4 4 4 4 12 12 12 12 12 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:""
*/
#include<stdio.h>
#include<stdlib.h>
    struct node{
        int a;
        int *x;
    };
  
int main(){
    int i,j;
    // struct node set1;
      //  struct node set2;
        struct rect {
            struct node set1;
        struct node set2;
        };
        struct rect r;
    scanf("%d\n",&(r.set1.a));
    r.set1.x=(int*)malloc(sizeof(int)*(r.set1.a));
    for(i=0;i<(r.set1.a);i++){
        scanf("%d ",&(r.set1.x[i]));
    }
   scanf("\n%d\n",&(r.set2.a));
   r.set2.x=(int*)malloc(sizeof(int)*(r.set2.a));
    for(i=0;i<(r.set2.a);i++){
        scanf("%d ",&(r.set2.x[i]));
    }
    for(i=0;i<(r.set2.a);i++){
        for(j=0;j<(r.set1.a);j++){
            if(r.set2.x[i]==r.set1.x[i])
            printf("%d ",r.set2.x[i]);
            else;
        }
    }
    return 0;
}