/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 4 5", ExpOutput:"1 2 3 4 5 
", Output:"1 2 3 4 5 "
Verdict:ACCEPTED, Visibility:1, Input:"5
5 4 3 2 1", ExpOutput:"1 2 3 4 5 
", Output:"1 2 3 4 5 "
Verdict:ACCEPTED, Visibility:1, Input:"4
1 3 2 1", ExpOutput:"1 1 2 3 
", Output:"1 1 2 3 "
Verdict:ACCEPTED, Visibility:1, Input:"6
1 4 3 2 1 0", ExpOutput:"0 1 1 2 3 4 
", Output:"0 1 1 2 3 4 "
Verdict:ACCEPTED, Visibility:1, Input:"10
1 4 3 2 1 0 5 8 100 110", ExpOutput:"0 1 1 2 3 4 5 8 100 110 
", Output:"0 1 1 2 3 4 5 8 100 110 "
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1
42", ExpOutput:"42 
", Output:"42 "
Verdict:ACCEPTED, Visibility:0, Input:"11
1 4 3 2 1 0 5 8 100 110 -10", ExpOutput:"-10 0 1 1 2 3 4 5 8 100 110 
", Output:"-10 0 1 1 2 3 4 5 8 100 110 "
*/
#include<stdio.h>
#include<stdlib.h>

void shift(int *pt,int l,int r){
    for(int i=r;i>l;i--){
        pt[i]=pt[i-1];
    }
}
int main(){
    int n;
    scanf("%d",&n);
    int *A=(int *)malloc(sizeof(int)*n);
    for(int i=0;i<n;i++){
        scanf("%d",A+i);
    }
    for(int i=1;i<n;i++){
        if(A[i]<A[i-1]){
            for(int j=0;j<i;j++){
                if(A[j]>A[i]){
                    int backup=A[i];
                    shift(A,j,i);
                    A[j]=backup;
                    break;
                }
            }
        }
    }
    for(int i=0;i<n;i++){
        printf("%d ",A[i]);
    }
    return 0;
}
