/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"1 5 7 2", ExpOutput:"The second largest number is 5", Output:"The second largest number is 5"
Verdict:ACCEPTED, Visibility:1, Input:"8 6 4 2", ExpOutput:"The second largest number is 6", Output:"The second largest number is 6"
Verdict:ACCEPTED, Visibility:0, Input:"1 10 15 3", ExpOutput:"The second largest number is 10", Output:"The second largest number is 10"
Verdict:ACCEPTED, Visibility:0, Input:"1 3 3 2 ", ExpOutput:"The second largest number is 3", Output:"The second largest number is 3"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1 2", ExpOutput:"The second largest number is 1", Output:"The second largest number is 1"
*/
//We are dealing with a programming to find the second largest numbers... 
#include<stdio.h>

int main()
{
    int a, b, c, d;//a, b, c, d are 4 natural nos.
    
    scanf("%d %d %d %d",&a, &b, &c, &d);//Will take the input from                                                 the users.
    if(a>b>c>d){
        printf("The second largest number is %d",c);}
    else if(a>b>d>c){
        printf("The second largest number is %d",d);}
    else if(a>c>b>d){
        printf("The second largest number is %d",b);}
    else if(a>c>d>b){
        printf("The second largest number is %d",d);}
    else if(a>d>b>c){
        printf("The second largest number is %d",b);}
    else if(a>d>c>b){
        printf("The second largest number is %d",c);}
    else if(b>c>d>a){
        printf("The second largest number is %d",d);}
    else if(b>c>a>d){
        printf("The second largest number is %d",a);}
    else if(b>a>c>d){
        printf("The second largest number is %d",c);}
    else if(b>a>d>c){
        printf("The second largest number is %d",d);}
    else if(b>d>a>c){
        printf("The second largest number is %d",a);}
    else if(b>d>c>a){
        printf("The second largest number is %d",c);}
    else if(c>d>a>b){
        printf("The second largest number is %d",a);}
    else if(c>d>b>a){
        printf("The second largest number is %d",b);}
    else if(c>a>b>d){
        printf("The second largest number is %d",b);}
    else if(c>a>d>b){
        printf("The second largest number is %d",d);}
    else if(c>b>a>d){
        printf("The second largest number is %d",a);}
    else if(c>b>d>a){
        printf("The second largest number is %d",d);}
    else if(d>a>b>c){
        printf("The second largest number is %d",b);}
    else if(d>a>c>b){
        printf("The second largest number is %d",c);}
    else if(d>b>a>c){
        printf("The second largest number is %d",a);}
    else if(d>b>c>a){
        printf("The second largest number is %d",c);}
    else if(d>c>a>b){
        printf("The second largest number is %d",a);}
    else{
        printf("The second largest number is %d",b);}
        

    return 0;
}