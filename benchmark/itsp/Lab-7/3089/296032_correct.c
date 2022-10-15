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
#include <string.h>
int index(char a1[50],char b1)
{
    int i;
    for (i=0;i<50;i++)
    {
        if (a1[i]==b1)
        {
            return i;
        }
    }
    return -1;
}
int strlength(char a2[50])
{
    int l=0,j;
    for (j=0;j<50;j++)
    {
        if (a2[j]!='\0')
        {
            l = l+1;
        }
        return l+1;
    }
    
}
int main() {
	char s1[50],s2[50],c1;
	scanf("%s\n",s1);
	scanf("%c\n",&c1);
	scanf("%s",s2);
	char s3[100];
	int i,j;
	
	if ((index(s1,c1))==0)
	{
        for (i=0;i<(strlen(s1)+strlen(s2));i++)
        {
            if (i<strlen(s2))
	        s3[i]=s2[i];
	        else
	        s3[i]=s1[(i-strlen(s2))];
        }
	    printf("%s",s3);
	}
	else if (index(s1,c1)>0)
	{
        for (j=0;j<index(s1,c1);j++)
	    {
            s3[j]=s1[j];
	    }
	    int k=0;
	    for (j=index(s1,c1);j<(index(s1,c1)+strlen(s2));j++)
	    {
	        s3[j]=s2[k];
	        k++;
	    }
	    int l = index(s1,c1);
	    for (j=(index(s1,c1)+strlen(s2));j<(strlen(s1)+strlen(s2));j++)
	    {
	        s3[j]=s1[l];
	        l++;
	    }
	    printf("%s",s3);
	}
	else
	{
        printf("%s",s1);
	}
	    
	
	return 0;
}