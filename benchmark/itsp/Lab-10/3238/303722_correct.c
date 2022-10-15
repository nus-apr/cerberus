/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"18 abcxyzdefxyzghixyz
3 xyz
2 uv", ExpOutput:"abcuvdefuvghiuv
", Output:"abcuvdefuvghiuv"
Verdict:ACCEPTED, Visibility:1, Input:"16 hello,howareyou?
3 are
4 were", ExpOutput:"hello,howwereyou?
", Output:"hello,howwereyou?"
Verdict:ACCEPTED, Visibility:1, Input:"20 abcdhefghighehiklmhe
2 he
4 hehe", ExpOutput:"abcdhehefghighehehiklmhehe
", Output:"abcdhehefghighehehiklmhehe"
Verdict:ACCEPTED, Visibility:1, Input:"18 hihellohihellohiih
2 hi 
5 hello", ExpOutput:"hellohellohellohellohelloih
", Output:"hellohellohellohellohelloih"
Verdict:ACCEPTED, Visibility:0, Input:"14 hihellohihello
3 hii
2 hi", ExpOutput:"hihellohihello
", Output:"hihellohihello"
*/
#include <stdio.h>
#include <stdlib.h>

int length(char *s1)     // Returns the length of the string
{
    int i;
    for(i=0;s1[i]!='\0';i++)
    {
    }
    return i;
}


int check_string(char *s,char *f)// Tells the user has                                  the substring has occured 
{
    int i;
    for(i=0;f[i]!='\0';i++)
    {
        if(f[i]!=s[i])
        {
            return 1;
        }
    }
return 0;
    
}

void replace_substring(char *s,char *t,char *w)
{
    int i;
    for(i=0;s[i]!='\0';i++)
    {
        if(s[i]==t[0]&&check_string(s+i,t)==0)
        {
            printf("%s",w);
            i=i+length(t)-1;// Cause it will be incremented once more
        }
        else 
        printf("%c",s[i]);
    }
        
}


int main()
{
	char *s1,*s2,*s3;   // The three strings
	int n1,n2,n3;   // For the length of the three strings
    scanf("%d",&n1);
    s1=(char*)malloc((n1+1) * sizeof(char));
    scanf("%s",s1);
    scanf("%d",&n2);
    s2=(char*)malloc((n2+1) * sizeof(char));
    scanf("%s",s2);
    scanf("%d",&n3);
    s3=(char*)malloc((n3+1) * sizeof(char));
    scanf("%s",s3);
   // printf("%s",s1);
    //printf("%s",s2);
   // printf("%s",s3);
    replace_substring(s1,s2,s3);
	return 0;

}