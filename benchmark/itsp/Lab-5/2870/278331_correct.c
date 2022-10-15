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

int check_prime(int num)
{int a;
 if(num==1)
 return 1;
 for(a=2;a<=num/2;a++)
 {if(num%a==0)
  return 1;
 }
  return 0;
} 

int main(){
    int N,c,p;
    scanf("%d",&N);
    for(p=N;;p++)
    {c=check_prime(p);
     if(c==0)
     break;
    }
    printf("%d",p);
    return 0;
}