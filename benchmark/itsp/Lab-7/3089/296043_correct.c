/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcxy 
b 
hi", ExpOutput:"ahibcxy", Output:"ahibcxy"
Verdict:ACCEPTED, Visibility:1, Input:"jhggd 
g 
sdfghjk", ExpOutput:"jhsdfghjkggd", Output:"jhsdfghjkggd"
Verdict:ACCEPTED, Visibility:1, Input:"dfghj 
j 
cvb", ExpOutput:"dfghcvbj", Output:"dfghcvbj"
Verdict:ACCEPTED, Visibility:1, Input:"d 
d 
asdfg", ExpOutput:"asdfgd", Output:"asdfgd"
Verdict:ACCEPTED, Visibility:1, Input:"Thisproblemhasnoautomatedtestcases.
.
----isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases----isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases----isn'tit?."
Verdict:ACCEPTED, Visibility:0, Input:"qwerty 
q 
zxcvb", ExpOutput:"zxcvbqwerty", Output:"zxcvbqwerty"
Verdict:ACCEPTED, Visibility:0, Input:"qwerty 
a 
zxcvb", ExpOutput:"qwerty", Output:"qwerty"
Verdict:ACCEPTED, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
,
zxcvb", ExpOutput:"Thisproblemhasnoautomatedtestcases.", Output:"Thisproblemhasnoautomatedtestcases."
Verdict:ACCEPTED, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
.
,,isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases,,isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases,,isn'tit?."
*/
#include <stdio.h>
void mod_str(char s1[50],char s2[50],char s[100],char c1)//
{  
    int j=0,count=0,i;
    for(i=0;i<100;i++)
    {
        if(s1[i]!='\0'&&s1[i]!=c1)
        {
            s[i]=s1[i];
            count++;
        }
        else
        if(s1[i]!='\0'&&s1[i]==c1)
        {
            while(s2[j]!='\0')
            {
                s[i]=s2[j];
                j++;
                i++;
            }
            break;
        }
    }
    while(i<100)
    {
        if(s1[count]!='\0')
        {
            s[i]=s1[count];
            count++;
            i++;
        }
        else
        if(s1[count]=='\0')
        {
            s[i]='\0';
            break;
        }
    }
}
int main() {
	char str1[50],str2[50],str[100],a;
	scanf("%s %c %s",str1,&a,str2);
	mod_str(str1,str2,str,a);
	printf("%s",str);
	return 0;
}