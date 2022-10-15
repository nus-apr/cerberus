/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"1 2 3 4 5 6 
", Output:"1 2 3 4 5 6 "
Verdict:ACCEPTED, Visibility:1, Input:"3
3 2 4
5
9 2 1 4 6", ExpOutput:"1 2 3 4 6 9 
", Output:"1 2 3 4 6 9 "
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 5 6
6
-6 -4 -2 -1 2 4
", ExpOutput:"-6 -4 -2 -1 1 2 3 4 5 6 
", Output:"-6 -4 -2 -1 1 2 3 4 5 6 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
1
1
", ExpOutput:"1 
", Output:"1 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
4
3 5 6 7
", ExpOutput:"1 3 5 6 7 
", Output:"1 3 5 6 7 "
Verdict:ACCEPTED, Visibility:0, Input:"3
9 2 1
3
1 2 9
", ExpOutput:"1 2 9 
", Output:"1 2 9 "
Verdict:ACCEPTED, Visibility:0, Input:"7
28 49 23 29 02 69 34
8
23 49 12 93 34 21 43 54", ExpOutput:"2 12 21 23 28 29 34 43 49 54 69 93 
", Output:"2 12 21 23 28 29 34 43 49 54 69 93 "
*/
#include <stdio.h>
#include <stdlib.h>

int main() {
    struct sets {
        int len;
        int *arr;
    };
    struct sets s1, s2;
    
    scanf("%d", &s1.len);
    s1.arr = (int *) malloc(sizeof(int)*s1.len);
    for (int i = 0; i < s1.len; i++) {
        scanf("%d", &s1.arr[i]);
    }
    
    scanf("%d", &s2.len);
    s2.arr = (int *) malloc(sizeof(int)*s2.len);
    for (int i = 0; i < s2.len; i++) {
        scanf("%d", &s2.arr[i]);
    }
    
    int *uset;
    uset = (int *) malloc(sizeof(int)*(s1.len + s2.len));
    int x = 0;
    
    for (int i = 0; i < s1.len; i++) {
        *(uset + x) = s1.arr[i];
        x++;
    }
    
    for (int i = 0; i < s2.len; i++) {
        int repeated = 0;
        for (int j = 0; j < s1.len; j++) {
            if (s1.arr[j] == s2.arr[i]) {
                repeated = 1;
            }
        }
        if (repeated == 0) {
            *(uset + x) = s2.arr[i];
            x++;
        }
    }
    int y = x;
    while (1) {
        int swaps = 0;
        for (int i = 0; i < x-1; i++) {
            if (uset[i] > uset[i+1]) {
                int t = uset[i];
                uset[i] = uset[i+1];
                uset[i+1] = t;
                swaps++;
            }
        }
        if (swaps == 0) break;
    }
    
    for (int i = 0; i < y; i++) {
        printf("%d ", uset[i]);
    }
    
    return 0;
}