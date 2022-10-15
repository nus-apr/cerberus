/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"12345", ExpOutput:"Reverse of 12345 is 54321", Output:"Reverse of 12345 is 54321"
Verdict:ACCEPTED, Visibility:1, Input:"1331", ExpOutput:"Reverse of 1331 is 1331", Output:"Reverse of 1331 is 1331"
Verdict:ACCEPTED, Visibility:1, Input:"100", ExpOutput:"Reverse of 100 is 1", Output:"Reverse of 100 is 1"
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"Reverse of 0 is 0", Output:"Reverse of 0 is 0"
Verdict:ACCEPTED, Visibility:0, Input:"10", ExpOutput:"Reverse of 10 is 1", Output:"Reverse of 10 is 1"
*/
#include<stdio.h>
int main()
{
    int num,n1,n2,n3,n4,n5;
    scanf("%d",&num);
    n5=num%10;
    n4=((num%100)-n5)/10;
    n3=((num%1000)-n5-(n4*10))/100;
    n2=((num%10000)-n5-(n4*10)-(n3*100))/1000;
    n1=num/10000;
    if(num>=10000)
    printf("Reverse of %d is %d%d%d%d%d",num,n5,n4,n3,n2,n1);
    else if((num>1000)&&(num<9999))
    printf("Reverse of %d is %d%d%d%d",num,n5,n4,n3,n2);
    else if((num>100)&&(num<999))
    printf("Reverse of %d is %d%d%d",num,n5,n4,n3);
    else if((num>10)&&(num<99))
    printf("Reverse of %d is %d%d",num,n5,n4);
    else if((num==10000)||(num==1000)||(num==100)||(num==10))
    printf("Reverse of %d is 1",num);
    else
    printf("Reverse of %d is %d",num,n5);
    return 0;
}