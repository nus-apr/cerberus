/*numPass=7, numTotal=9
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
Verdict:WRONG_ANSWER, Visibility:1, Input:"Add-automated/pre-generated-test-cases-to-this-problem.
pre
com", ExpOutput:"Add-automated/compre-generated-test-cases-to-this-problem.", Output:"Add-automated/compre-generated-test-cases-to-this-problem.l"
Verdict:ACCEPTED, Visibility:0, Input:"mississippi 
pp 
troll", ExpOutput:"mississitrollppi", Output:"mississitrollppi"
Verdict:ACCEPTED, Visibility:0, Input:"underground
under
water", ExpOutput:"waterunderground", Output:"waterunderground"
Verdict:ACCEPTED, Visibility:0, Input:"imindian 
indian 
proud", ExpOutput:"improudindian", Output:"improudindian"
Verdict:WRONG_ANSWER, Visibility:0, Input:"Add-automated/pre-generated-test-cases-to-this-problem.
/pre
-human", ExpOutput:"Add-automated-human/pre-generated-test-cases-to-this-problem.", Output:"Add-automated-human/pre-generated-test-cases-to-this-problem.l"
*/
#include <stdio.h>

int main() {
	char str[50],str1[50],str2[50],str3[50],str4[50];
	scanf("%s",str);
	//printf("\n");
	scanf("%s",str1);
	//printf("\n");
	scanf("%s",str2);
	int i,j,k,n,idx=-1,m;
	for(i=0;str[i]!='\0';i++)
	{
	   m=0;
	   idx=i;
	   for(j=0;str1[j]!='\0';j++)
	         {
	             //printf("%c --- %c\n",str[i+j],str1[j]);
	          if(str[i+j]!=str1[j])
	          {
	              m=1;
	              break;
	          }
	          }
	          if(m==0)
	          break;
	}
	//printf("%d\n",idx);
	//printf("%d\n",m);
	if(m==0)
	{
    	for(k=0;k<idx;k++)
     	{
	        str3[k]=str[k];   
     	}
        	str3[k]='\0';
        	//printf("%s\n",str3);
     	for(n=idx,i=0;str[n]!='\0';n++,i++)
	    {
	        //printf("%c",str[n]);
	         str4[i]=str[n];
     	}
        	 str4[n]='\0';
        	 //printf("%s\n",str4);
        	 printf("%s%s",str3,str2);
        	 for(int i=0;str4[i]!=0;++i)
        	    printf("%c",str4[i]);
	 	
	    }
	else printf("%s",str);      
	
	
	return 0;
}