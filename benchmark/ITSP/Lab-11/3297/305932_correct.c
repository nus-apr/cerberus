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
void func1(int a[],int n,int i){
    int j=0,l=0,k;
    for(j=0;j<n;j++){
        if(a[j]>a[i]){
            k=a[j];
            a[j]=a[i];
            for(l=i-1;l>=j+1;l--){
                a[l+1]=a[l];
            }
            a[j+1]=k;
            break;
        }
    } 
}
int main(){
    int *a,n,i=0,j=1;
    scanf("%d",&n);
    a=(int *)malloc(n*sizeof(int ));
    for(i=0;i<n;i++){
        scanf("%d",(a+i));
    }
    for(i=1;i<n;i++){
        if (a[i]>a[i-1])
            continue;
        else 
            func1(a,n,i);
    }
    for(i=0;i<n;i++){
        printf("%d ",a[i]);
    }
    return 0;
}