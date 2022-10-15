/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 -2 3 -5 5", ExpOutput:"3
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9
1 2 -9 3 21 5 41 6 70", ExpOutput:"6
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
-1 2 5 -7 9", ExpOutput:"4
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9
21 23 1 34 123 324 12 213 3423", ExpOutput:"6
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
99 -12 14 56 987 34", ExpOutput:"4
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
-1 45 98 -2 103", ExpOutput:"4
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 -2 46", ExpOutput:"2
", Output:"1"
*/
#include <stdio.h>


int main() {
    int a,b,c=1,N,i,j,n=1;
      scanf("%d",&N);
      int A[N],MaxTill[N];
     for(a=0;a<N;a++)
         {scanf("%d",&b);
          A[a]=b;
         }
        MaxTill[0]=1;
        for(i=1;i<N;i++)
           {n=1;
               for(j=0;j<i;j++)
                 {if(j<i && A[j]<A[i])         
                    {if(MaxTill[j]>n)
                      {n=MaxTill[j]+1;}
                    }
                 }
                
            MaxTill[i]=n;
              
            
       }   
     int m,x;
     m=0;
     for(x=0;x<N;x++)
       {if(MaxTill[x]>m)
           {m=MaxTill[x];}
       }
     printf("%d",m);  
}