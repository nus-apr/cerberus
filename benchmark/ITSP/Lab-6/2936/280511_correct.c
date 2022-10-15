/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"4
11 2 18 2", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"8
1 21 34 45 53 65 71 8", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 2 3 4 1", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>

int main() {
	int N,i,j,c=1;
	scanf("%d\n",&N);
	int arr[50];
	for(i=0;i<N;i++) scanf("%d ",&arr[i]);
	for(i=0;i<N-1;i++){
	    for(j=i+1;j<N;j++){
	        if(arr[i]==arr[j]){
	            c=0;
	            break;
	        }
	
	    }
	    if(!c) break;
	    
	}
	if(!c)
	    printf("YES");
	else
	    printf("NO");
	return 0;
}