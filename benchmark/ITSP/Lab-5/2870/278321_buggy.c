/*numPass=1, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"14", ExpOutput:"17
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"24", ExpOutput:"29
", Output:""
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"2
", Output:"2"
Verdict:WRONG_ANSWER, Visibility:1, Input:"68", ExpOutput:"71
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"99", ExpOutput:"101
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"150", ExpOutput:"151
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"200", ExpOutput:"211
", Output:""
*/
#include<stdio.h>

int check_prime(int num){
    int i,c=2,p=0;
      if(num==1 || num==2){
          return 2;
      }
      else
      {
        while(p==0)
        {
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