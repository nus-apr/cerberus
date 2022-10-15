/*numPass=3, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"12345", ExpOutput:"Reverse of 12345 is 54321", Output:"Reverse of 12345 is 3413"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1331", ExpOutput:"Reverse of 1331 is 1331", Output:"Reverse of 1331 is 38"
Verdict:ACCEPTED, Visibility:1, Input:"100", ExpOutput:"Reverse of 100 is 1", Output:"Reverse of 100 is 1"
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"Reverse of 0 is 0", Output:"Reverse of 0 is 0"
Verdict:ACCEPTED, Visibility:0, Input:"10", ExpOutput:"Reverse of 10 is 1", Output:"Reverse of 10 is 1"
*/
#include<stdio.h>
#include<math.h>

int main()
{
    // Fill this area with your code.
    int a,b,c,d=10,e,f,g,h=0,i,j=0,k,l;
    double m,n;
    scanf("%d",&a);
    l=a;
    
    for (c=100;c>=1;)
    {
     c=a/d;
     d=d*10;
     h=h+1;
    } 
      k=h;
    
    
    for (i=1;i<=h;i=i+1)
    {
     b=a%10;
     a=a-b;
     a=a/10;
     m=pow(b,k);
     j=j+m;
     k=k-1;
     
     
    } 
    printf("Reverse of %d is %d",l,j);
    
    
    

    return 0;
}