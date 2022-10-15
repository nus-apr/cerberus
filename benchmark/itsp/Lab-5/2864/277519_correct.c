/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:ACCEPTED, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"2 3 5 7 11 13 17 19 "
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>

int check_prime(int num){

//Complete the function definitions here.
    int j,r;
    if (num==1)
    return 0;
    for(j=2;j<num;j++){
        r=num%j;
        if(r==0)
        return 0;
    }
    return 1;
}    
int main(){
	//Enter your code here
	int a,n1,n2,num;
	scanf("%d %d",&n1,&n2);
	for(num=n1;num<=n2;num++){
	   a=check_prime(num);
	   if(a!=0)
	   printf("%d ",num);
	}
	return 0;
}