/*numPass=1, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 4 5", ExpOutput:"1111
1  1
1  1
1  1
1111
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5 6", ExpOutput:"22222
2   2
2   2
2   2
2   2
22222
", Output:"2"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9 6 7", ExpOutput:"999999
9    9
9    9
9    9
9    9
9    9
999999
", Output:"11"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 4 5", ExpOutput:"3333
3  3
3  3
3  3
3333
", Output:"3"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 2 2", ExpOutput:"22
22
", Output:"2"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 3", ExpOutput:"333
3 3
333
", Output:"3"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1", ExpOutput:"1
", Output:"1"
*/
#include<stdio.h>

int check_prime(int num){
     
       int i;
       for(i=2;i<num;i++){
           if(num%i==0){
          num++;
           i=2;
           }
          else { 
           continue;
          }
           }
           
           
       
       printf("%d",num);
}
       
 int main() {
   
   int N;
   scanf("%d",&N);
   check_prime(N);
    
    
    
    
    return 0;
}