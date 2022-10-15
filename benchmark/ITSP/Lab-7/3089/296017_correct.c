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

int main() 
{
    char ch,s1[50],s2[50];
    int l1=0,l2=0,i,j,c=0;
    
    scanf("%s\n",s1);
    scanf("%c\n",&ch);
    scanf("%s",s2);
    
    while(s1[l1]!='\0'||s2[l2]!='\0')
    {
        if(s1[l1]!='\0')
        l1++;
        if(s2[l2]!='\0')
        l2++;
        
    }
    
    for(i=0;i<l1;i++)
    {
        if( (ch==s1[i]||s1[i]=='\0') && c==0)
        {
            c=1;
        printf("%s",s2);
        }
        printf("%c",s1[i]);
        
        
    }
    
    
    
	// Fill this area with your code.
	return 0;
}