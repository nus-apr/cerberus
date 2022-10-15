/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2 -3 -8 -13 -8 -3 2 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"20 15 10 5 10 15 20 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4 -1 -6 -11 -6 -1 4 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"16 11 6 1 6 11 16 "
*/
#include <stdio.h>
   int p;
   int func2(int n){
          printf("%d ",n);
          if(n==p)
          {return 0;
          }
          return func2(n+5);
          
      }
       
    int func(int n){
        int x;
        x=n;
       printf("%d ",x);
       if (x>(p-15))
       return func(n-5);
       if (x<=(p-15))
       {
       return func2(x+5);}
        
    }
      
      
       
       
       
   

int main(){
    int n;
    scanf("%d",&n);
    p=n;
  
    
    func(n);
    
    
    
    
	return 0;
}