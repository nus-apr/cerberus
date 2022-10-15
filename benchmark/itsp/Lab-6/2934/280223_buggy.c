/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
52 91 72 65 100", ExpOutput:"100 
100 65 
100 65 72 
100 65 72 91 
100 65 72 91 52 
", Output:"52 
52 91 
52 91 72 
52 91 72 65 
52 91 72 65 100 
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
1 22 333", ExpOutput:"333 
333 22 
333 22 1 
", Output:"1 
1 22 
1 22 333 
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10
2346 62 756 452 7274 288 2 81 82 1000", ExpOutput:"1000 
1000 82 
1000 82 81 
1000 82 81 2 
1000 82 81 2 288 
1000 82 81 2 288 7274 
1000 82 81 2 288 7274 452 
1000 82 81 2 288 7274 452 756 
1000 82 81 2 288 7274 452 756 62 
1000 82 81 2 288 7274 452 756 62 2346 
", Output:"2346 
2346 62 
2346 62 756 
2346 62 756 452 
2346 62 756 452 7274 
2346 62 756 452 7274 288 
2346 62 756 452 7274 288 2 
2346 62 756 452 7274 288 2 81 
2346 62 756 452 7274 288 2 81 82 
2346 62 756 452 7274 288 2 81 82 1000 
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6 
-2 6 18 27 5 2", ExpOutput:"2 
2 5 
2 5 27 
2 5 27 18 
2 5 27 18 6 
2 5 27 18 6 -2 
", Output:"-2 
-2 6 
-2 6 18 
-2 6 18 27 
-2 6 18 27 5 
-2 6 18 27 5 2 
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8 
-182 571 -27 257 21 9199 -299 12", ExpOutput:"12 
12 -299 
12 -299 9199 
12 -299 9199 21 
12 -299 9199 21 257 
12 -299 9199 21 257 -27 
12 -299 9199 21 257 -27 571 
12 -299 9199 21 257 -27 571 -182 
", Output:"-182 
-182 571 
-182 571 -27 
-182 571 -27 257 
-182 571 -27 257 21 
-182 571 -27 257 21 9199 
-182 571 -27 257 21 9199 -299 
-182 571 -27 257 21 9199 -299 12 
"
*/
#include <stdio.h>

void print_array(int a[],int size)
{
    int i,j;
    
    for(i=1;i<=size;i++) //outer loop for N lines
    {
    for(j=0;j<i;j++) //inner loop
     printf("%d ",a[j]);
    
    printf("\n"); //change line after each iteration 
    }
}


int main() {
   
  int i;  
  int a[100]; //array of integers
  int N;   //size of array
	     
  scanf("%d \n",&N); // input size
	        
 for(i=0;i<N;i++) //intput elements
    scanf("%d ",&a[i]);
	        
 print_array(a,N); //function call to print array 
	
	return 0;
}