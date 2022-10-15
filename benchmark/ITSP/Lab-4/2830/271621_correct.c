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
    scanf("%d %d %d %d",&a,&b,&c,&d);        //input 4 numbers.
    int second;
       if(a<b)
         {
             int s=a;
             a=b;
             b=s;
         }
       if(c<d)
         {
             int s=c;
             c=d;
             d=s;
         }
       if(b<c)
         {
             int s=b;
             b=c;
             c=s;
         }
       if(a<b)
         {
             int s=a;
             a=b;
             b=s;
         }
       if(b<c)
         {
             int s=b;
             b=c;
             c=s;
         }
       if(c<d)
         {
             int s=c;
             c=d;
             d=s;
         }
    printf("The second largest number is %d",b);     
    return 0;
}