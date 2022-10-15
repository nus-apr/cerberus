/*
<b>NEW</b>: Constraints on a[i] updated to : -10000 <= a[i] <= 10000 

ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly
- Function use and modular programming
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Given a number N, and an array a[0...N-1] which has N numbers, print the following - 

a[N-1]
a[N-1] [N-2]
a[N-1] a[N-2] a[N-3]
....
.....
a[N-1] a[N-2] .... a[0]

Note: 
1. Remember, there are spaces between consecutive numbers.
2. Clearly, there are N lines to be printed. 

Input format : 
The first line contains a single integer, N. 
The second line contains N space separated integers, specifying a[0], a[1], ... , a[N-1]

Constraints : 
1 <= N <= 5555
-10000 <= a[i] <= 10000 

Example:

Input:
5
52 91 72 65 100

Output:
100 
100 65 
100 65 72 
100 65 72 91 
100 65 72 91 52
*/
#include<stdio.h>

int main (){
    int N, a[5555];
    scanf ("%d", &N);
    for (int i=0; i<N;++i)scanf ("%d", &a[(N-1)-i]);
    for (int i=0; i<N;++i){
        for (int j=0; j<=i;++j){
            printf ("%d ", a[j]);
        }   
        printf ("\n");
    }
    return 0;
}