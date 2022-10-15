/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14", ExpOutput:"NO
", Output:"0NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2", ExpOutput:"YES
", Output:"2YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"8
1 21 34 45 53 65 71 8", ExpOutput:"NO
", Output:"0NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 2 3 4 1", ExpOutput:"YES
", Output:"2YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:"0NO"
*/
#include <stdio.h>


int main() {
	int ch ,i,j,count=0;
	scanf("%d",&ch);
	int s [ch];
	for(i=0;i<ch;i++)
	{ scanf("%d",&s[i]);}
 for(i=0;i<ch;i++)
 {for(j=0;j<ch;j++)
{  if(s[i]==s[j]&&i!=j)
 {count=count+1;}
    
}
    
}
printf("%d",count);
if (count>0)
{ printf("YES");}
else
{printf("NO");}
	return 0;
}