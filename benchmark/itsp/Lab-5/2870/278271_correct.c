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

int check_prime(int num);
int check_prime(int num){//Complete function definitions
 if (num==1){
     return 0;
 }
  int i;
  for(i=2;i<num;i++){
      if(num%i!=0)
      continue;
      else 
      return 0;
 }    
      return num;
}     
int main(){
    
 int n,x;
  scanf("%d",&n);
  for(x=n;x>=n;x++){
   if (check_prime(x))
  {
        break;
    }else
    {
    continue;
}
}
    printf("%d",x);
   return 0;
}