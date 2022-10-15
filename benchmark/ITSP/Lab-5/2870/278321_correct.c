/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"14", ExpOutput:"17
", Output:"17"
Verdict:ACCEPTED, Visibility:1, Input:"24", ExpOutput:"29
", Output:"29"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"2
", Output:"2"
Verdict:ACCEPTED, Visibility:1, Input:"68", ExpOutput:"71
", Output:"71"
Verdict:ACCEPTED, Visibility:0, Input:"99", ExpOutput:"101
", Output:"101"
Verdict:ACCEPTED, Visibility:0, Input:"150", ExpOutput:"151
", Output:"151"
Verdict:ACCEPTED, Visibility:0, Input:"200", ExpOutput:"211
", Output:"211"
*/
#include<stdio.h>

int check_prime(int num){
    int i,p=0;
      if(num==1 || num==2){
          return 2;
      }
      else
      {
        while(p==0)
        { int c=2;
          for(i=2;i<=num-1;i++)
          { 
              if((num%i)!=0)
              { c++;
              }
          }
          if(c==num)
          {
              p=num;
          }
          else
          {
              num++;
          }
        }
        return p;
      }
    };

//Complete function definitions

int main(){
    int N;
    scanf("%d",&N);
    int req_no=check_prime(N);
    printf("%d",req_no);
    
    
    return 0;
}