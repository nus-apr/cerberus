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
	//program to generate rectangle like figure
	/*         width
	           ----
	           3333
               3  3
               3  3  }height
               3  3
               3333      */
	int num,wid,hig,a,b;
	//enter number to be printed
	//width of rectangle 
	//height of rectangle
	scanf("%d %d %d",&num,&wid,&hig);
	for(a=1;a<=hig;a++)
	{
	    for(b=1;b<=wid;b++)
	    {
	        if(a==1||a==hig)
	        {
	            printf("%d",num);
	        }
	        else if(b==1||b==wid)
	        {
	            printf("%d",num);
	        }
	        else
	        {
	            printf(" ");
	        }
	    }
	    printf("\n");
	}
	return 0;
}