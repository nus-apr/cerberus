/*numPass=7, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"defabc"
Verdict:ACCEPTED, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"mmingaprogr"
Verdict:ACCEPTED, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"ogrammerrhello-@p"
Verdict:ACCEPTED, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"abab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"dearohell0C"
Verdict:WRONG_ANSWER, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"mmingprogaC"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"dzcab"
Verdict:ACCEPTED, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"cba"
Verdict:ACCEPTED, Visibility:0, Input:"a", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
void swap(char c[],int r)
{
    char t[r];
    if(r%2==0)
    {
        for(int i=0;i<r/2;i++)
        {
            t[i]=c[i+r/2];
        }
        for(int j=r/2;j<r;j++)
        {
            t[j]=c[j-r/2];
        }
    }
    else
    {
        for(int i=0;i<r/2;i++)
        {
            t[i]=c[i+r/2+1];
        }
        for(int j=r/2+1;j<r;j++)
        {
            t[j]=c[j-r/2-1];
        }
        t[r/2]=c[r/2];
    }
    //t[r]='\0';
    printf("%s",t);
}
int main() 
{
	char s[100];
    int x=0;
	scanf("%s",s);
    for(int j=0;j<100;j++)
    {
        if(s[j]=='\0')
        {
            x=j;
            break;
        }    
    }
    swap(s,x);
	return 0;
}