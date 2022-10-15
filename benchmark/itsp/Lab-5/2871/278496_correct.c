/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"1 4 5", ExpOutput:"1111
1  1
1  1
1  1
1111
", Output:"1111
1  1
1  1
1  1
1111
"
Verdict:ACCEPTED, Visibility:1, Input:"2 5 6", ExpOutput:"22222
2   2
2   2
2   2
2   2
22222
", Output:"22222
2   2
2   2
2   2
2   2
22222
"
Verdict:ACCEPTED, Visibility:1, Input:"9 6 7", ExpOutput:"999999
9    9
9    9
9    9
9    9
9    9
999999
", Output:"999999
9    9
9    9
9    9
9    9
9    9
999999
"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"3333
3  3
3  3
3  3
3333
", Output:"3333
3  3
3  3
3  3
3333
"
Verdict:ACCEPTED, Visibility:1, Input:"2 2 2", ExpOutput:"22
22
", Output:"22
22
"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 3", ExpOutput:"333
3 3
333
", Output:"333
3 3
333
"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1", ExpOutput:"1
", Output:"1
"
*/
#include<stdio.h>

int main(){
	int N,w,h;
	scanf("%d%d%d",&N,&w,&h);
	int i,j;
	i=1;
	for(i=1;i<=h;i++)
	{
	     if(i==1||i==h)
	     {
	        for(j=1;j<=w;j++)
	        printf("%d",N);
	     }
	     else
	     {
	        printf("%d",N);
	        for(j=2;j<w;j++)
	        printf(" ");
	        printf("%d",N);
	     }
	        printf("\n");
	}       
	return 0;
    }
