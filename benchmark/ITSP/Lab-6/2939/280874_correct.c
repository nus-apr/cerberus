/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
1 -2 3 -5 5", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"9
1 2 -9 3 21 5 41 6 70", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:1, Input:"5
-1 2 5 -7 9", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:1, Input:"9
21 23 1 34 123 324 12 213 3423", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"6
99 -12 14 56 987 34", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"5
-1 45 98 -2 103", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 -2 46", ExpOutput:"2
", Output:"2"
*/
#include <stdio.h>

int max(int a,int b) {
    return ((a>b)*a)+((a<=b)*b); 
}
int main() {
	// Fill this area with your code.
	int n,i,j,count; 
	scanf("%d\n",&n);
	int ar[n],mt[n];
	for(count=0; count!=n; count++) {
	    scanf("%d ", &ar[count]); 
	    mt[count]=1; 
	    
	}
	int msq=1; 
	for(i=0; i!=n; i++) {
	    for(j=i-1; j>=0; j--) {
	        //printf("\n%d %d", ar[i],ar[j]);
	        if(ar[j]<ar[i]) {
	            if(mt[i]<1+mt[j]) mt[i]=mt[j]+1; 
	        }
	        //printf(" %d ", mt[i]);
	    }
	msq=max(mt[i],msq);
	    
	}
    printf("%d",msq);
	return 0; 
}