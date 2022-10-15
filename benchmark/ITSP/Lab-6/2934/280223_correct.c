/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"5
52 91 72 65 100", ExpOutput:"100 
100 65 
100 65 72 
100 65 72 91 
100 65 72 91 52 
", Output:"100 
100 65 
100 65 72 
100 65 72 91 
100 65 72 91 52 
"
Verdict:ACCEPTED, Visibility:1, Input:"3
1 22 333", ExpOutput:"333 
333 22 
333 22 1 
", Output:"333 
333 22 
333 22 1 
"
Verdict:ACCEPTED, Visibility:1, Input:"10
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
", Output:"1000 
1000 82 
1000 82 81 
1000 82 81 2 
1000 82 81 2 288 
1000 82 81 2 288 7274 
1000 82 81 2 288 7274 452 
1000 82 81 2 288 7274 452 756 
1000 82 81 2 288 7274 452 756 62 
1000 82 81 2 288 7274 452 756 62 2346 
"
Verdict:ACCEPTED, Visibility:0, Input:"6 
-2 6 18 27 5 2", ExpOutput:"2 
2 5 
2 5 27 
2 5 27 18 
2 5 27 18 6 
2 5 27 18 6 -2 
", Output:"2 
2 5 
2 5 27 
2 5 27 18 
2 5 27 18 6 
2 5 27 18 6 -2 
"
Verdict:ACCEPTED, Visibility:0, Input:"8 
-182 571 -27 257 21 9199 -299 12", ExpOutput:"12 
12 -299 
12 -299 9199 
12 -299 9199 21 
12 -299 9199 21 257 
12 -299 9199 21 257 -27 
12 -299 9199 21 257 -27 571 
12 -299 9199 21 257 -27 571 -182 
", Output:"12 
12 -299 
12 -299 9199 
12 -299 9199 21 
12 -299 9199 21 257 
12 -299 9199 21 257 -27 
12 -299 9199 21 257 -27 571 
12 -299 9199 21 257 -27 571 -182 
"
*/
#include <stdio.h>

void print_array(int a[],int size)
{
    int i,j,k;
    
    for(i=1;i<=size;i++) //outer loop for N lines
    {
    for(j=0,k=size-1;j<i;k--,j++) //inner loop
     printf("%d ",a[k]);
    
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