/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"20 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"16 "
*/
#include <stdio.h>
int n;
void res(int a)
{
    static int count=0;
    if (count==0)
    {
      printf("%d ",a);
      count++;
    }
    //else
    //{
        if(a!=n)
        {
            printf("%d ",a);
            if (a>0)
            {
              res(a-5);
            }
            else
            res(a+5);
        }    
    //}    
}
int main(){
    scanf("%d",&n);
    res(n);
	return 0;
}