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
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>

int main() {
int N;
int k;
scanf("%d",&N);
int a[N];
for(k=0;k<N;k++){
    scanf("%d",&a[k]);
}
int j;
int s=0;
int i;
for(i=0;i<N-1;i=i+1){
for(j=i+1;j<N;j=j+1){
   if(a[i]==a[j]){
   s=1+s;  
       
   }
   else{
       s=0;
   }
}    
}
if(s==0){
    printf("NO");
}
    else{
        printf("YES");
    }
	return 0;
}