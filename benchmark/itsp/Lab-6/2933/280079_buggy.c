/*numPass=2, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14
2
13 42", ExpOutput:"YES
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
3
3 2 1", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 3 6 1
2
1 6", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 3 5 7 9
2
2 4", ExpOutput:"NO
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"5
9 9 8 9 9
2
9 9", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>

int main() {
     int N1,N2,a[50],b[50],k,x,y;
     scanf("%d",&N1);  //no. of elements in a[]
     for(int i=0;i<N1;i++)
     {
         scanf("%d",&a[i]);
     }
     scanf("%d",&N2);
     
     for(int i=0;i<N2;i++)
     {
         scanf("%d",&b[i]);
	 }
	for(k=0;k<=N1-N2+1;k++)
	{
	    int count=0,x=k,y=0;
	while((x<k+N2)&&(y<=N2-1))
	{
	    if(a[x]==b[y])
	    count++;
	    x++;
	    y++;
	}
	
	if(count==N2)
	{
	    printf("YES");
	    break;
	}
	else if((count!=N2)&&(a==N1-N2+1))
	printf("NO");
	}
	return 0;
}