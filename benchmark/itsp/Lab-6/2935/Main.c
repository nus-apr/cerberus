/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly 
- Function use and modular programming
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Multiply two polynomials together. 

Input : 
The first line will contain two space separated numbers, n1 and n2 - respectively the degrees of the first and second polynomials. 
The second line will contain the first polynomial, that is space separated (n1 + 1) terms. The i'th term is the coefficient of x^(i-1). The coefficient of x^n1 will be non-zero.
The third line will contain the second polynomial, that is space separated (n2 + 1) terms. The i'th term is the coefficient of x^(i-1). The coefficient of x^n2 will be non-zero.
Each coefficient will be a number in [-1000, 1000].

Output the third polynomial, in a similar format. The degree on the first line, followed by the coefficients in the next line. The i'th term should be the coefficient of x^(i-1) in the new polynomial.

Constraints : 
1 <= n1, n2 <= 15

Example:

Input:
2 2
3 1 -5
0 -2 4

(-5x^2 + x + 3)*(4x^2 - 2x) = -20x^4 + 14x^3 + 10x^2 - 6x + 0. So, output:
4
0 -6 10 14 -20
*/
#include<stdio.h>

int main (){
    int n1, n2, n;
    scanf ("%d %d", &n1, &n2);
    n = n1 + n2;
    printf ("%d\n", n);
    int p1[20], p2[20], p[40];
    for (int i=0;i<=n1;++i)scanf ("%d", &p1[i]);
    for (int i=0;i<=n2;++i)scanf ("%d", &p2[i]);
    
    for (int i=0;i<=n;++i)p[i] = 0;
    for (int i=0;i<=n1;++i){
        for (int j=0;j<=n2;++j){
            p[i+j]+=p1[i]*p2[j];
        }  
    }
    for (int i=0;i<=n;++i)printf ("%d ", p[i]);
    return 0;
}