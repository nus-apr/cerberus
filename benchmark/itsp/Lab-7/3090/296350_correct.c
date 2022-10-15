/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"jhggd 
g 
sdfghjk", ExpOutput:"jhsdfghjkggd", Output:"jhsdfghjkggd"
Verdict:ACCEPTED, Visibility:1, Input:"abcde 
bc 
re", ExpOutput:"arebcde", Output:"arebcde"
Verdict:ACCEPTED, Visibility:1, Input:"jhukfi 
kf 
tred", ExpOutput:"jhutredkfi", Output:"jhutredkfi"
Verdict:ACCEPTED, Visibility:1, Input:"mississippi 
ss 
troll", ExpOutput:"mitrollssissippi", Output:"mitrollssissippi"
Verdict:ACCEPTED, Visibility:1, Input:"Add-automated/pre-generated-test-cases-to-this-problem.
pre
com", ExpOutput:"Add-automated/compre-generated-test-cases-to-this-problem.", Output:"Add-automated/compre-generated-test-cases-to-this-problem."
Verdict:ACCEPTED, Visibility:0, Input:"mississippi 
pp 
troll", ExpOutput:"mississitrollppi", Output:"mississitrollppi"
Verdict:ACCEPTED, Visibility:0, Input:"underground
under
water", ExpOutput:"waterunderground", Output:"waterunderground"
Verdict:ACCEPTED, Visibility:0, Input:"imindian 
indian 
proud", ExpOutput:"improudindian", Output:"improudindian"
Verdict:ACCEPTED, Visibility:0, Input:"Add-automated/pre-generated-test-cases-to-this-problem.
/pre
-human", ExpOutput:"Add-automated-human/pre-generated-test-cases-to-this-problem.", Output:"Add-automated-human/pre-generated-test-cases-to-this-problem."
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
	char str2[50];
	scanf("%s\n",str);
	scanf("%s",str1);
	scanf("%s",str2);
	int count=length(str);
	int count1=length(str1);
	int count2=length(str2);
	
	int i=0,j=0;
	
	int size=0;
	
	while(str[i]!='\0'&&str[j]!='\0'&&j<count1&&i<count)
	{ if(str[i]==str1[j])
	    {
	        i++;
	        size++;
	        j++;
	        
	        if(size==count1)
	        break;
	    }
	
	 else if((str[i]!=str1[j])&&(str[i-1]==str1[j-1])&&i>0&&j>0)
	    {
	       size=0;
	       i++;
	       j=0;
	    }	
         	
	 else
	    { i++;}
	
	}
	int k,l;
	if(size==count1)
	{ for(k=0;k<i-count1;k++)
	    {printf("%c",str[k]);}
	   for(l=0;l<count2;l++) 
	    {printf("%c",str2[l]);}
	    for(k=i-count1;k<count;k++)
	    {printf("%c",str[k]);}
	    
	}

	
	return 0;
}