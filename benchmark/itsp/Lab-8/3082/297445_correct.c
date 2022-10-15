/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 3
1 1 1
1 1 1
1 1 1", ExpOutput:"0 1 2 
", Output:"0 1 2 "
Verdict:ACCEPTED, Visibility:1, Input:"3 4
1 2 3 4
10 20 17 15
-10 -19 -2 -1", ExpOutput:"1 
", Output:"1 "
Verdict:ACCEPTED, Visibility:1, Input:"5 5
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
", ExpOutput:"0 1 2 3 4 
", Output:"0 1 2 3 4 "
Verdict:ACCEPTED, Visibility:0, Input:"3 3
-1 -2 -3
-4 -5 -6
-7 -8 -9", ExpOutput:"0 
", Output:"0 "
Verdict:ACCEPTED, Visibility:0, Input:"3 3 
-1 -1 -1
-1 -1 -1
-1 -1 -1", ExpOutput:"0 1 2 
", Output:"0 1 2 "
*/
#include <stdio.h>

int a[100];//a[i] will store the sum of elements of the ith row of the matrix M

int readmax(int M[100][100],int m,int n);//This is the prototype for readmax() which will input the elements,compute the sum of ith row,store it in a[i],evaluate the maximum sum and return it

int readmax(int M[100][100],int m,int n){
  
  int i,j,sum=0,max;
   
   
     
      sum=0;  
     
      for(j=0;j<m;j++){
         
         scanf("%d",&M[i][j]);
         sum+=M[0][j];
      
         }
     
     a[0]=sum;
     max=sum;
      
     for(i=1;i<n;i++){
         
     sum=0;
     
     for(j=0;j<m;j++){
         
        scanf("%d",&M[i][j]); 
         sum+=M[i][j];
         
     }
     
     a[i]=sum;
     
     if(sum>max) 
       
       max=sum;
   
       
   }
 
  return max;  

    
}

int main() {
  
  int M[100][100],max,m,n,i;
   
   scanf("%d %d",&n,&m);
    
    max=readmax(M,m,n);
	
	 for(i=0;i<n;i++){
	
	   if(a[i]==max)
	   
	     printf("%d ",i);
	    
	}
	
  return 0;

    
}