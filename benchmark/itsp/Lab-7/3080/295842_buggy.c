/*numPass=7, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>
int length(char s[])
{
    int i=0;
    for (i=0;i<=100;i++)
      {
       if(s[i]=='\0')
       break;
      }
return i;
}
int main() {
	char s1[101],s2[101],c;
	int i,x=0,j,k,y=0,n,l1,l2;
	 scanf("%s\n",s1);
	 scanf("%c\n",&c);
	 scanf("%d\n",&n);
	 scanf("%s",s2);
	
	l1=length(s1);
	l2=length(s2);
	
	for(i=0;i<l1;i++)
	{
	    if(s1[i]==c)
	    x++;
	}

	if(l1>=l2)
	 {
	   for(j=0;j<l1;j++)
	    {
	        y=0;
	      if(s1[j]==s2[0])
	        {
	            for(k=0;k<l1;k++)
	              {
	                if(s1[j+k]==s2[k])
	                  y++;
	                else
	                  break;
	              }
	              if(y==(l2))
	              break;
	        }
	    }
	 }

	if(x<n||y==(l2))
	{
      if(x<n&&y==(l2))
        printf("NO");
      else
        printf("YES");
	}
    else
      printf("NO");
      
	return 0;
}