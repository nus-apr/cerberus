/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"1 5 7 2", ExpOutput:"The second largest number is 5", Output:"The second largest number is 5"
Verdict:ACCEPTED, Visibility:1, Input:"8 6 4 2", ExpOutput:"The second largest number is 6", Output:"The second largest number is 6"
Verdict:ACCEPTED, Visibility:0, Input:"1 10 15 3", ExpOutput:"The second largest number is 10", Output:"The second largest number is 10"
Verdict:ACCEPTED, Visibility:0, Input:"1 3 3 2 ", ExpOutput:"The second largest number is 3", Output:"The second largest number is 3"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1 2", ExpOutput:"The second largest number is 1", Output:"The second largest number is 1"
*/
#include<stdio.h>

int main()
{
int a,b,c,d;
scanf("%d%d%d%d",&a,&b,&c,&d);
if(a>=b&&a>=c&&a>=d&&b>=c&&b>=d){
    printf("The second largest number is %d",b);
    return 0;
}
if(a>=b&&a>=c&&a>=d&&c>=d&&c>=b){
    printf("The second largest number is %d",c);
    return 0;
}
if(a>=b&&a>=c&&a>=d&&d>=b&&d>=c){
    printf("The second largest number is %d",d);
    return 0;
}
if(b>=a&&b>=c&&b>=d&&a>=c&&a>=d){
    printf("The second largest number is %d",a);
    return 0;
}
if(b>=a&&b>=c&&b>=d&&c>=a&&c>=d){
    printf("The second largest number is %d",c);
    return 0;
}
if(b>=a&&b>=c&&b>=d&&d>=c&&d>=a){
    printf("The second largest number is %d",d);
    return 0;
}
if(c>=a&&c>=b&&c>=d&&a>=b&&a>=d){
    printf("The second largest number is %d",a);
    return 0;
}
if(c>=a&&c>=b&&c>=d&&b>=a&&b>=d){
    printf("The second largest number is %d",b);
    return 0;
}
if(c>=a&&c>=b&&c>=d&&d>=a&&d>=b){
    printf("The second largest number is %d",d);
    return 0;
}
if(d>=a&&d>=b&&d>=c&&a>=b&&a>=c){
    printf("The second largest number is %d",a);
    return 0;
}
if(d>=a&&d>=b&&d>=c&&b>=a&&b>=c){
    printf("The second largest number is %d",b);
    return 0;
}
if(d>=a&&d>=b&&d>=c&&c>=a&&c>=b){
    printf("The second largest number is %d",c);
    return 0;
}
    return 0;
}