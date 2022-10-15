/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 20"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 10"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 35"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 84"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 4"
*/
#include<stdio.h>

int main()
{int N,count=0;int i=1,j=1,k=1;
scanf("%d",&N);
 for(i=1;i<=N;i++)
  {for(j=1;j<=i;j++)
   {for(k=1;k<=j;k++)
     { if(i<(j+k)||j<(i+k)||k<(i+j))
        count=count+1;}
       
   }}
   printf("Number of possible triangles is %d",count);
   
 
 
    // Fill this area with your code.
    return 0;
}