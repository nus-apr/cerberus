/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 1"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 1"
*/
#include<stdio.h>

int main()
{ int N;
int i,j,k;
 int count=0; 
 scanf("%d",&N);
  for (i=1; i<=N; i++);  
  {
      for (j=i; j<=N; j=j+1);
     {
         for (k=j; k<=N; k=k+1);
     {     if (i+j>k && j+k>i && i+k>j)
     count=count+1;
     }
     }
  } 
  printf ("Number of possible triangles is %d",count);
    return 0;
}