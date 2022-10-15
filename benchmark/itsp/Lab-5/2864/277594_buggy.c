/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"1 2 3 5 7 11 13 17 19 "
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>

int check_prime(int num){
  int i=1;
for(i=2;i<num;i=i+1) 
   {
       if (num%i==0)
       return(0); /* not a prime number */
   }
  
    return(1); /* its a prime number */
     
}
      
int main(){
int n1,n2,i,result;   /* result here denotes if the given number is                                    prime or not */
scanf("%d %d ",&n1,&n2);
for(i=n1;i<=n2;++i){
 result=check_prime(i); /*calls for the function */
      if (result==1){
         printf("%d ",i);
      }
}
	return 0;
}