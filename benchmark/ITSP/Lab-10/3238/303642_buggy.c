/*numPass=2, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"18 abcxyzdefxyzghixyz
3 xyz
2 uv", ExpOutput:"abcuvdefuvghiuv
", Output:"abcuvdefuvghiuv"
Verdict:ACCEPTED, Visibility:1, Input:"16 hello,howareyou?
3 are
4 were", ExpOutput:"hello,howwereyou?
", Output:"hello,howwereyou?"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 abcdhefghighehiklmhe
2 he
4 hehe", ExpOutput:"abcdhehefghighehehiklmhehe
", Output:"abcdhehefgigheheiklmhehe"
Verdict:WRONG_ANSWER, Visibility:1, Input:"18 hihellohihellohiih
2 hi 
5 hello", ExpOutput:"hellohellohellohellohelloih
", Output:"helloellohelloellohelloi"
Verdict:WRONG_ANSWER, Visibility:0, Input:"14 hihellohihello
3 hii
2 hi", ExpOutput:"hihellohihello
", Output:"ielloiello"
*/
#include <stdio.h>
#include <stdlib.h>

// Write any other auxillary functions here 

void replace_substring(char *s,char *t,char *w)
{
    ;// Write your code here
}

int main()
{
	int n1,n2,n3;
	scanf("%d ",&n1);
	char *a=(char*)malloc(n1*sizeof(char)+1);
	scanf("%s",a);
	scanf("%d ",&n2);
	char *b=(char*)malloc(n1*sizeof(char)+1);
	scanf("%s",b);
	scanf("%d ",&n3);
	char *c=(char*)malloc(n1*sizeof(char)+1);
	scanf("%s",c);
    
    int i,j,count;
    for(i=0;i<n1;i++)
    {
        if(b[0]==a[i])
        {
            count=0;
            for(j=0;j<n2;j++)
            {
                if(a[i+j]==b[j])
                {
                    count++;
                }
            }
            if(count==n2)
            {
                for(j=0;j<n2;j++)
                {
                    a[i+j]='\0';
                }
                printf("%s",c);
            }
        }
        else
        {
            printf("%c",a[i]);
        }
    }
	

	return 0;

}