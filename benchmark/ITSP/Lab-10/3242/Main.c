/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.
 - Pointers are to be used to get the value. Submissions without explicit use of pointers would be given 0 marks. 
 - Recursion is to be used. Other analytic methods of computing would not fetch marks. 
 - All matrices are to be dynamically created - remember, you can treat matrices as an array of arrays.
  
Determinant is a very important property of square matrices. Interestingly, it can be computed in a recursive fashion as follows :
Let A(n,n) be a matrix of size n x n. Let us define M(j,k) = sub-matrix of A which does not contain the row j and column k. Clearly, the matrix M would be a square matrix of size (n-1)x(n-1). We can calculate det(A) as follows :

det(A) = sum over any row or column (((-1)^(j + k)) * det( M(j,k) ).
I.e. while applying the above recursion formula, keep one of j or k fixed. 

Example: For the 3x3 matrix A we can use the above formula with j=1 fixed and varying k :-
det(A) = det(M(1,1)) - det(M(1,2)) + det(M(1,3)) .

INPUT :
An integer n denoting the size of the square matrix.
n lines of n integers each denoting the contents of the matrix. 

OUTPUT :
Determinant of the matrix.

You need to write a C program to calculate the determinant of a matrix.
*/
#include <stdio.h>
#include <stdlib.h>

/*
   Recursive definition of determinate using expansion by minors.
*/

int Determinant(int **a,int n)
{
   int i,j,j1,j2;
   int det = 0;
   int **m = NULL;

   if (n < 1) { /* Error */

   } else if (n == 1) { /* Shouldn't get used */
      det = *(*(a + 0) + 0);
   } else if (n == 2) {
      det = (**a) * *(*(a + 1) + 1) - **(a + 1) * *(*a + 1);
   } else {
      det = 0;
      for (j1=0;j1<n;j1++) {
         m = malloc((n-1)*sizeof(int *));
         for (i=0;i<n-1;i++)
            m[i] = malloc((n-1)*sizeof(int));
         for (i=1;i<n;i++) {
            j2 = 0;
            for (j=0;j<n;j++) {
               if (j == j1)
                  continue;
               m[i-1][j2] = *(*(a + i) + j);
               j2++;
            }
         }
         det += pow(-1,1+j1+1) * *(*a + j1) * Determinant(m,n-1);
         for (i=0;i<n-1;i++)
            free(m[i]);
         free(m);
      }
   }
   return(det);
}


int main(){

	int n ,i, j; 
	scanf("%d" , &n);

	int **m = malloc((n)*sizeof(int *));
	for (i=0 ; i<n ; i++)
            m[i] = malloc((n)*sizeof(int));

    // Scanning the matrix
    for (i=0;i<n;i++)
    	for (j = 0 ; j < n ; j++)
    		scanf("%d" , *(m + i ) +  j);

    printf("%d" , Determinant(m , n ));
    return 0;
}