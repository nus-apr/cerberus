/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcxy 
b 
hi", ExpOutput:"ahibcxy", Output:"abcxyb"
Verdict:WRONG_ANSWER, Visibility:1, Input:"jhggd 
g 
sdfghjk", ExpOutput:"jhsdfghjkggd", Output:"jhggdg"
Verdict:WRONG_ANSWER, Visibility:1, Input:"dfghj 
j 
cvb", ExpOutput:"dfghcvbj", Output:"dfghjj"
Verdict:WRONG_ANSWER, Visibility:1, Input:"d 
d 
asdfg", ExpOutput:"asdfgd", Output:"dd"
Verdict:WRONG_ANSWER, Visibility:1, Input:"Thisproblemhasnoautomatedtestcases.
.
----isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases----isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases.."
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty 
q 
zxcvb", ExpOutput:"zxcvbqwerty", Output:"qwertyq"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty 
a 
zxcvb", ExpOutput:"qwerty", Output:"qwertya"
Verdict:WRONG_ANSWER, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
,
zxcvb", ExpOutput:"Thisproblemhasnoautomatedtestcases.", Output:"Thisproblemhasnoautomatedtestcases.,"
Verdict:WRONG_ANSWER, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
.
,,isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases,,isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases.."
*/
#include <stdio.h>
int strl(char str[])
{
    int i=0,count=0;
    while((i<100)&&(str[i]!='\0'))
    {
        count = count + 1;
        i = i+1;
    }
    return count;
}
int main()
{
	char str1[50],str2[50],ch,str[100];
	scanf("%s",str1);
	scanf("%c",ch);
	printf("%c",ch);
	scanf("%s",str2);
	int m=strl(str2);
	int i=0,co=0;
	while((i<50)&&(str1[i]!=ch))
	{
	    str[i]=str1[i];
	    co = co+1;
	    i=i+1;
	}
	int j=0;
	while((j<m)&&(str2[j]!='\0'))
	{
	    str[i]=str2[j];
	    j=j+1;
	    i=i+1;
	}
	int k=0;
	while((k<50)&&(str[co+k]!='\0'))
	{
	    str[i]=str1[co+k];
	    k=k+1;
	    i=i+1;
	}
	printf("%s",str);
	return 0;
}