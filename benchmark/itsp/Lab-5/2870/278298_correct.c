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

int check_prime(int num) //Defined a Function called 'check_prime'
{
    int N,x; //Defined 2 Variable,One For Number Other for Division
    N=num;   //Stored Value of Input in N
    x=2;     //Initialised The Value Of X as 2
          for (x=2;x<N;) //Created a Division Process Loop
            {
              if ((N%x)!=0) //If Number is Not Divisble By X, then
               {x=x+1;}     //Incremented The Value Of X
              else          //Otherwise
               {N=N+1;
                x=2;        //Again Put x=2 for Division Loop
               }     //Incremented The Value of N
            }
 return x;  //The Output is Returned in x
    
}                     

int main(){  //Main Body
    
    int A;
    scanf("%d",&A);
    printf("%d",check_prime(A)); //Used The Function for Input 22
    
    return 0;                    
}