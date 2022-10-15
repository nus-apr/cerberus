/*numPass=2, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"10"
Verdict:ACCEPTED, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"55"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"19969"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"-1195"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"13"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"56503819"
*/
#include <stdio.h>

int main() {
    int d,N;
    scanf ("%d%d",&d,&N);
    int arr[100];
    for (int j=0; j<d; j++) {
        scanf ("%d",&arr[j]);
    }
    
    for (int k=d; k<=N; k++) {
        arr[k] =0;
        for (int m=k-1; m>=k-1-d; m--) {
            arr[k] = arr[k] + arr[m];
        }
    }
    
    
    printf ("%d",arr[N]);
	return 0;
}