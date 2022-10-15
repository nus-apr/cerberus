/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:1, Input:"4
11 2 18 2", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:1, Input:"8
1 21 34 45 53 65 71 8", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 2 3 4 1", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:"NO
"
*/
#include <stdio.h>

int main() {
int N;
scanf("%d\n",&N);
if (N<50){
    int d=0;
    int arr[N],i,j;
   for (i=0;i<N;i=i+1){
     scanf("%d ",&arr[i]);
 }    
	  for(i=0;i<N;i=i+1){    
         for(j=0;j!=i&&j<N;j=j+1){
             if(arr[i]==arr[j]){
                 d=1;break;}
         }    
            
	  }    
 if(d==0){
     printf("NO\n");
 }
 else{
     printf("YES\n");
 }
     
 }
	return 0;
}