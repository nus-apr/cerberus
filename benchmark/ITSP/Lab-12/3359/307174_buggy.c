/*numPass=4, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"1 2 3 4 5 6 
", Output:"1 2 3 4 5 6 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
3 2 4
5
9 2 1 4 6", ExpOutput:"1 2 3 4 6 9 
", Output:"3 2 4 9 2 1 4 6 "
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 5 6
6
-6 -4 -2 -1 2 4
", ExpOutput:"-6 -4 -2 -1 1 2 3 4 5 6 
", Output:"-6 -4 -2 -1 1 2 3 4 5 6 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
1
1
", ExpOutput:"1 
", Output:"1 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
4
3 5 6 7
", ExpOutput:"1 3 5 6 7 
", Output:"1 3 5 6 7 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
9 2 1
3
1 2 9
", ExpOutput:"1 2 9 
", Output:"1 2 9 2 1 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
28 49 23 29 02 69 34
8
23 49 12 93 34 21 43 54", ExpOutput:"2 12 21 23 28 29 34 43 49 54 69 93 
", Output:"23 28 49 12 49 23 29 2 69 34 93 34 21 43 54 "
*/
#include <stdio.h>
#include <stdlib.h>

struct sets{
    int n;
    int *a;
};

int main() {
    
    struct sets *pts;
     pts=(struct sets *)malloc(2*sizeof(struct sets));
     int i,j,k;
    
    for(i=0;i<2;i++)
 {   
    scanf("%d",&(pts[i].n));
    
    pts[i].a=(int *)malloc((pts[i].n)*sizeof(int));
    
    for(j=0;j<pts[i].n;j++)
     scanf("%d",&pts[i].a[j]);
 } 
 
    int *output;
    output=(int*)malloc((pts[0].n+pts[1].n)*sizeof(int));
    
    for(k=0,i=0,j=0;k<pts[0].n+pts[1].n;)
  {
      if(i==pts[0].n && j<pts[1].n)
        for(;j<pts[1].n;j++,k++)
       output[k]=pts[1].a[j];
        
        if(j==pts[1].n && i<pts[0].n)
        for(;i<pts[0].n;i++,k++)
       output[k]=pts[0].a[i]; 
         
    if(i<pts[0].n && j<pts[1].n)     
    {     
     if(pts[0].a[i]<pts[1].a[j])
      { output[k]=pts[0].a[i];
          i++;
          k++;}
          
     else
     {output[k]=pts[1].a[j];
     j++;
     k++;}
    }
    

  }   
    
    for(k=0;k<pts[0].n+pts[1].n;k++)
   { if(output[k]==output[k+1])
       k++;
      printf("%d ",output[k]);
      
   }  
    return 0;
}