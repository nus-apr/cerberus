/*numPass=5, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"89", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"59", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"109", ExpOutput:"Yes
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"131", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"123", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"125", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"141", ExpOutput:"Yes
", Output:"No"
*/
#include<stdio.h>

int check_prime(int num){
    int i=2,n;
    scanf("%d",&n);
    while(i<=num-1)
    {//using the while loop
        if(n%i==0) //if remainder of i and n is zero
            return 0;//return 0
        i=i+1;//increment in i
    }
    return 1;//else return1
    }
//

int main(){
    int n,flag=0;
    scanf("%d",&n);
    for(int x=2;x<=n-2;x++)
    {
    if(check_prime(x) && check_prime(n-x)){
        printf("Yes");
        flag=1;
        break;
    }
    }
    if(flag==0){
        printf("No");
    }
}

	
