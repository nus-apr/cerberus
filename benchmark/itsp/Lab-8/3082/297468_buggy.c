/*numPass=3, numTotal=5
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3
-1 -2 -3
-4 -5 -6
-7 -8 -9", ExpOutput:"0 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 
-1 -1 -1
-1 -1 -1
-1 -1 -1", ExpOutput:"0 1 2 
", Output:""
*/
#include <stdio.h>

	int a[100][100];
int m,n;

void max_sum(int n, int m){
    

int i,j,max[n],sum;
for(i=0;i<n;i++)
    max[i]=0;
//for(i=0;i<n;i++)
//for(j=0;j<m;j++)
  //         printf("%d ",a[i][j]);



int max2=0;
for(i=0;i<n;i++){
    sum=0;/*intialising sum with 0*/
for(j=0;j<m;j++){
    sum=sum+a[i][j];
}
if(sum>max2)
max2=sum;
max[i]=sum;

}
for(i=0;i<n;i++){


    if(max[i]==max2)/*if max is found*/
     {
         
         printf("%d ",i);/*print the elements of the corrospndin g row with max sum*/
     }
}

}

int main() {

	int m,n,i,j;
	scanf("%d %d",&n,&m);/*input*/
	for(i=0;i<n;i++)
	    for(j=0;j<m;j++)
	    scanf("%d",&a[i][j]);/*scanning the elements*/
	    		    
	    		    max_sum(n,m);/*function call*/

	 
	


	return 0;
}