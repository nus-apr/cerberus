/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14
2
13 42", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"6
1 2 3 4 5 6
3
3 2 1", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 3 6 1
2
1 6", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 3 5 7 9
2
2 4", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"5
9 9 8 9 9
2
9 9", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>

void read_into_array(int arr[], int size){
    for (int i = 0; i < size; i++){
        scanf("%d", &arr[i]);
    }
}

void check_subarray(int a[], int b[], int s1, int s2){
    int cnt = 0;
    for (int i = 0; i < s1; i++){
        if (a[i] == b[0]) {
            cnt = i;
            break;
        }
    }
    for (int i = 0; i < s2; i++){
        if (b[i] != a[i+cnt]) {
            printf("NO");
            return;
        }
    }
    printf("YES");
}

int main() {
	int n1, n2;
	scanf("%d", &n1);
	int A1[n1];
	read_into_array(A1, n1);
	scanf("%d", &n2);
	int A2[n2];
	read_into_array(A2, n2);
    check_subarray(A1, A2, n1, n2);
	return 0;
}