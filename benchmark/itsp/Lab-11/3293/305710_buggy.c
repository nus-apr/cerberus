/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 0 1
1 0 1 0
0 1 0 1
1 0 1 0 
2", ExpOutput:"1 2 1 2 ", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0 
3", ExpOutput:"1 2 3 2 ", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0
3", ExpOutput:"1 2 3 2 ", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"2
0 1
1 0
2", ExpOutput:"1 2 ", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1
0
2", ExpOutput:"1 ", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"4 
0 1 1 1 
1 0 1 1 
1 1 0 1 
1 1 1 0
1000", ExpOutput:"1 2 3 4 ", Output:""
*/
#include <stdio.h>
#include<stdlib.h>

int main(){
    int**a,n,c;
    scanf("%d",n);
    int *b;
     b=(int*)malloc(n*sizeof(int));//defining memory dynamically
   a=(int**)malloc(n*sizeof(int*));//defining memory dynamically
   for(int p=0;p<n;p++)
   {
       a[p]=(int*)malloc(n*sizeof(int));//defining memory dynamically
   }
   for(int i=0;i<n;i++)
   {
       for(int j=0;j<n;j++)
       {
           scanf("%d",a[i][j]);
       }
   }
   scanf("%d",&c);
 //  b[0]=1;
   for(int q=0;q<n;q++)
   {
       for(int r=0;r<n;r++)
       {
           if(a[q][r]==0)
           {
               b[q]=r+1;
               break;
           }
       }
   }
   for(int j=0;j<n;j++)
   {
       printf("%d ",b[j]);
   }
    
	return 0;
}