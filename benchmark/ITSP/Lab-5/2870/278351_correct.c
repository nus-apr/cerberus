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
    int i,j,a,p;
    for(i=num;;i++){p=1;
        for(j=2;j<=i-1;j++){
            a=i%j;
            if(a==0)break;
            
        }    
    if(a!=0)
     return(i);
    else
      continue;
    }
}
int main(){
    int N,p;
    scanf("%d",&N);
    if((N==1)||(N==2))
      printf("%d",2);
    else{
      p = check_prime(N);
      printf("%d",p);
    }
    return 0;
}