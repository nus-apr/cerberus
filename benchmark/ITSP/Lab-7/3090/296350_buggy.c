/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"jhggd 
g 
sdfghjk", ExpOutput:"jhsdfghjkggd", Output:"5
1
No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcde 
bc 
re", ExpOutput:"arebcde", Output:"5
2
No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"jhukfi 
kf 
tred", ExpOutput:"jhutredkfi", Output:"6
2
No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"mississippi 
ss 
troll", ExpOutput:"mitrollssissippi", Output:"11
2
No"
Verdict:WRONG_ANSWER, Visibility:1, Input:"Add-automated/pre-generated-test-cases-to-this-problem.
pre
com", ExpOutput:"Add-automated/compre-generated-test-cases-to-this-problem.", Output:"55
3
No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"mississippi 
pp 
troll", ExpOutput:"mississitrollppi", Output:"11
2
No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"underground
under
water", ExpOutput:"waterunderground", Output:"11
5
No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"imindian 
indian 
proud", ExpOutput:"improudindian", Output:"8
6
No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"Add-automated/pre-generated-test-cases-to-this-problem.
/pre
-human", ExpOutput:"Add-automated-human/pre-generated-test-cases-to-this-problem.", Output:"55
4
No"
*/
#include <stdio.h>
int length(char s[])
{   int i=0;
    while(s[i]!='\0')
    {
        i++;
    }
return i;
}
int main() {
	char str[50];
	char str1[50];
	
	scanf("%s\n",str);
	scanf("%s",str1);
	
	int count=length(str);
	int count1=length(str1);
	
	int i,j;
	int num=1;
	for(i=0;i<(count-count1);i++)
	{   
	    for(j=i;j<(i+count1);j++)
	    { 
	      if(str[i]!=str1[j])  
	       { num=0;
	         break;}
	    }
	    
	   if(num==1)
	   break;
	}
	
	printf("%d\n",count);
	printf("%d\n",count1);
	
	if(num==1)
	{printf("Yes");}
	
	else if(num==0)
	{printf("No");}
	
	
	
	return 0;
}