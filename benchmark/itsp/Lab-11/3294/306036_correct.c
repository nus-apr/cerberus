/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2 -3 2"
Verdict:ACCEPTED, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"20 15 10 5 0 5 10 15 20"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4 -1 4"
Verdict:ACCEPTED, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"16 11 6 1 -4 1 6 11 16"
*/
#include <stdio.h>
int n,count=0;
void res(int a)
{
    if(a<=0)
    count++;
    if(a!=n)
    {
        printf("%d ",a);
        if (count==0)
        {
          res(a-5);
        }
        else
        res(a+5);
    } 
    else
    {
        printf("%d",a);
        return;
    }
        
}
int main(){
    scanf("%d",&n);
    printf("%d ",n);
    res(n-5);
	return 0;
}