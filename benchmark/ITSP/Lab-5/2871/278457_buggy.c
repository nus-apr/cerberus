/*numPass=1, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 4 5", ExpOutput:"1111
1  1
1  1
1  1
1111
", Output:"11111  11  11  11111"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5 6", ExpOutput:"22222
2   2
2   2
2   2
2   2
22222
", Output:"222222   22   22   22   222222"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9 6 7", ExpOutput:"999999
9    9
9    9
9    9
9    9
9    9
999999
", Output:"9999999    99    99    99    99    9999999"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 4 5", ExpOutput:"3333
3  3
3  3
3  3
3333
", Output:"33333  33  33  33333"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 2 2", ExpOutput:"22
22
", Output:"2222"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 3", ExpOutput:"333
3 3
333
", Output:"3333 3333"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1", ExpOutput:"1
", Output:"1"
*/
#include<stdio.h>

int main(){
	int N,w,h;
	scanf("%d%d%d",&N,&w,&h);
	int i,j;
	for (i=1;i<=h;i++)
	{
	    for (j=1;j<=w;j++)
	    {
	        if ((j==1)||(j==w))
	        {
	            printf("%d",N);
	        }
	        else
	        {
	            if ((i==1)||(i==h))
	            {
	                printf("%d",N);
	            }
	            else
	            {
	                printf(" ");
	            }
	        }
	    }
	    
	}
	return 0;
}