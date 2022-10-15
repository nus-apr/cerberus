/*numPass=2, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcxy 
b 
hi", ExpOutput:"ahibcxy", Output:"abcxy"
Verdict:WRONG_ANSWER, Visibility:1, Input:"jhggd 
g 
sdfghjk", ExpOutput:"jhsdfghjkggd", Output:"jhggd"
Verdict:WRONG_ANSWER, Visibility:1, Input:"dfghj 
j 
cvb", ExpOutput:"dfghcvbj", Output:"dfghj"
Verdict:WRONG_ANSWER, Visibility:1, Input:"d 
d 
asdfg", ExpOutput:"asdfgd", Output:"d"
Verdict:WRONG_ANSWER, Visibility:1, Input:"Thisproblemhasnoautomatedtestcases.
.
----isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases----isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases."
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty 
q 
zxcvb", ExpOutput:"zxcvbqwerty", Output:"qwerty"
Verdict:ACCEPTED, Visibility:0, Input:"qwerty 
a 
zxcvb", ExpOutput:"qwerty", Output:"qwerty"
Verdict:ACCEPTED, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
,
zxcvb", ExpOutput:"Thisproblemhasnoautomatedtestcases.", Output:"Thisproblemhasnoautomatedtestcases."
Verdict:WRONG_ANSWER, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
.
,,isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases,,isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases."
*/
#include <stdio.h>

int main() {
	char s1[51],s2[51],s3[101],c1;
	scanf("%s",s1);
	scanf("%c",&c1);
	scanf("%s",s2);
	int i,j,k=0,flag=0;
	for(i=0;s1[i]!='\0';i++)
	{
	    if(s1[i]==c1 && flag==0)
	    {
	         for(j=0;s2[j]!='\0';j++)
	         s3[k++]=s2[j];
	         flag=1;
	    }      
	    s3[k++]=s1[i];
	}
	s3[k]='\0';
	printf("%s",s3);
	return 0;
}