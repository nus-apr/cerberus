/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:"icodingisfunNO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:"codingisfunNO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:"codeYES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:"ooYES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:"ooYES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:"atestcasemanuallyYES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:"atestcasemanuallyNO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:"atestcasemanuallyYES"
*/
#include <stdio.h>

int read_string(char str[])
{
    int i=0;
    char c;
    scanf("%c",&c);
    
    //while(c!='\n' && c!= (char)EOF)
    while((c>='A' && c<='Z') || (c>='a' && c<='z') || (c>='0' && c<='9'))
    {
        str[i]=c;
        scanf("%c",&c);
        i++;
    }
    
    str[i]='\0';
    
    return i;
    
}


int main() {
	
	char s1[200],s2[200],c;
	int i,j,n,l1,l2;
	
	l1=read_string(s1);
	
	scanf("%c",&c);
	scanf("%d",&n);
	
	l2=read_string(s2);
	printf("%s",s2);
	printf("%s",s1);
	
	int x=0;
	for(i=0;i<l1;i++)
	{
	    if(s1[i]==c)
	    {
	        x=x+1;
	    } 
	}
	int t=0;
	
	if(x<n)
	t=t+1;
	int h=0;
    for(i=0;i<l1;i++)
    {   int g=0;
        for(j=0;j<l2;j++)
        {
            if(s1[i+j]==s2[j])
            g=g+1;
        }
        if(g==l2)
        {
            h=1;
            break;
        }    
    }
    
    if(h==1)
    t=t+1;
    if(t==1)
    printf("YES");
    else
    printf("NO");	
	return 0;
}