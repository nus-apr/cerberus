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
#include <stdio.h>
#include <stdlib.h>

void i_am_groot(int arr[], int n, int i){
    int j, d;
    if(i==n)
        return;
    
    if(*(arr+i)<*(arr+i-1)){
        for(j=0; j<n; j++){
            if(*(arr+i)<*(arr+j)){
                d=*(arr+i);
                *(arr+i)=*(arr+j);
                *(arr+j)=d;
            }    
        }
        i_am_groot(arr, n, i+1);
    }
    
    else
        i_am_groot(arr, n, i+1);
}

int main(){
    int i, n;
    int* x;
    scanf("%d\n", &n);
    x= (int*)calloc(n+1 , sizeof(int));
    for(i=0; i<n; i++){
        scanf("%d", (x+i));
    }
    i_am_groot(x, n, 1);
    for(i=0; i<n; i++){
        printf("%d ", *(x+i));
    }
    free(x);
	return 0;
}