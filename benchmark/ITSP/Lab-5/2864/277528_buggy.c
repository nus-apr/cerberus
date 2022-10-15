/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"1 2 3 5 7 11 13 17 19 "
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>

int check_prime(int num);
void print_prime(int n1, int n2);

int check_prime(int num){
    /* The function returns 1 if num is prime otherwise it return 0 */
    int i; // i: for the iteration in for loop
    for(i=2;i<num;i++)
    {
        if(num%i==0)
        {
            return 0;
            /* if the number would be divisible it won't be prime */
        }
    }
    return 1;
}

void print_prime(int n1, int n2){
    /* The function calls function check_prime()
       and prints prime numbers */
    int i; //for the iteration in for loop
    for(i=n1;i<=n2;i++)
    {
        if(check_prime(i))
            printf("%d ",i);
    }
}

int main(){
	int n1,n2; //To store the input limits
	scanf("%d%d",&n1,&n2);//to receive input from user
	print_prime(n1,n2);
	return 0;
}