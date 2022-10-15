/*numPass=3, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"8
1 21 34 45 53 65 71 8", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 2 3 4 1", ExpOutput:"YES
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>
int check(int a[],int n){
    int i,j,b=n;
    for(i=1;i<b;i++){
        for(j=0;j<i;j++){
            if(a[i]==a[j]){
                return 0;
            }
            
        }
    }
    return 1;
}

    



   


int main() {
	int n,i,k;
	scanf("%d/n",&n);
	int a[n];
	for(i=0;i<n;i++){
        scanf("%d",&a[i]);
    }
    k=check(a[n],n);
    if(k==0){
        printf("YES");
    }
    if(k==1){
        printf("NO");
    }
	
	return 0;
}