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
{
    int i,count=0;
    for(i=1;i<=num;i++)
    {if((num%i)==0)
count++;
}if(count>2)
return 1;
else
return 0;
}

//Complete function definitions

int main(){
    
int num,check,i,count=0;
scanf("%d",&num);
if(num==1)
printf("2");
else{
check=check_prime(num);
if(check==0)
printf("%d",num);
else
{
    for(i=num+1;i<=num+20;i++)
    {
    check=check_prime(i);
    if(check==0)
    break;}
    printf("%d",i);
}



}
    return 0;
}