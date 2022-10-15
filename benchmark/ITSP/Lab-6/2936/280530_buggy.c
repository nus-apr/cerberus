/*numPass=3, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"8
1 21 34 45 53 65 71 8", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 2 3 4 1", ExpOutput:"YES
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>

int main() {
    int N;
    int a[50];
    while(N<=50){
        scanf("%d",&N);
    }
    
    
    int v=0;
    int i;
    int j;
    
    for(i=0;i<=N-1;i++)
    
    {
        for(j=0;j<=N-1;j++)
    
        {
            if(a[i]==a[j] && i!=j)
            {
                v=1;
                
            } 
            
        }
    }    
        
    
      if(v==1)
     {
         printf("YES");
     }
          else
          {
              printf("NO");
          }
                
            
             
              
        
    
    

	
	

	   
	
	return 0;
}