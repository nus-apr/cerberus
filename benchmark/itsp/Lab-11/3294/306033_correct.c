/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2 -3 2 "
Verdict:ACCEPTED, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"20 15 10 5 0 5 10 15 20 "
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4 -1 4 "
Verdict:ACCEPTED, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"16 11 6 1 -4 1 6 11 16 "
Verdict:ACCEPTED, Visibility:0, Input:"8", ExpOutput:"8 3 -2 3 8 ", Output:"8 3 -2 3 8 "
*/
#include <stdio.h>
    int a[100];

void pat(int n,int q,int i){
    while(i<=(q/2)){
    a[i]=n;
    a[q-i-1]=n;
    return pat(n-5,q,i+1);
    }

    
}

int main(){
    int x;
    scanf("%d",&x);
    int q;
    if(x%5==0)q = 2*(x/5) + 1;
    else{
        q = 2*(x/5) + 3;
    }

    
    int i=0;
    pat(x,q,i);
    for(i=0;i<q;i++){
        printf("%d ",a[i]);
    }
    
    
    
	return 0;
}