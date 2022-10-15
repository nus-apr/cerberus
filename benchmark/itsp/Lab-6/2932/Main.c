/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly 
- Function use and modular programming

<b>[NEW]: One hidden test case updated. </b>
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

A d-order recurrence relation for a sequence {a} is defined as,
a[i] = b[i]   ; for 0 <= i  < d
a[i] = a[i-1] + a[i-2] + .... + a[i-d]

Given d, b[0...d-1], N, find the value of a[N].

Input format : 
1st line contains the number d and N (separated by space).
2nd line contains d space-separated numbers, representing b[0...d-1]

Constraints : 
Every 'number' means an integer in [-1000, 1000]
0 <= N <= 30
1 <= d <= 20
The output will fit in an int variable.

Example:
Input:
4 4
1 2 3 4

Here, a[4] = a[3]+a[2]+a[1]+a[0] = 1+2+3+4 = 10. So, output:
10

Input:
5 0
55 32 56 12 83

Output:
55

*/
#include<stdio.h>
#define MAXN 31
#define MAXD 21

int main (){
    int N, d;
    scanf("%d\n%d", &d, &N);
    int a[MAXN], b[MAXD];
    for (int i=0;i<d;++i){
        scanf("%d", &b[i]);
        a[i]=b[i];
    }
    for (int i=d;i<=N;++i){
        a[i] = 0;
        for (int j=1;j<=d;++j)
            a[i] += a[i-j];
    }
    printf ("%d\n", a[N]);
    return 0;
}