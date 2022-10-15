/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"18 abcxyzdefxyzghixyz
3 xyz
2 uv", ExpOutput:"abcuvdefuvghiuv
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"16 hello,howareyou?
3 are
4 were", ExpOutput:"hello,howwereyou?
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 abcdhefghighehiklmhe
2 he
4 hehe", ExpOutput:"abcdhehefghighehehiklmhehe
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"18 hihellohihellohiih
2 hi 
5 hello", ExpOutput:"hellohellohellohellohelloih
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"14 hihellohihello
3 hii
2 hi", ExpOutput:"hihellohihello
", Output:""
*/
#include <stdio.h>
#include <stdlib.h>
int str_len(char s[])
{int i;
    for(i=0;s[i]!='\0';++i);
    return i;
}
void replace_substring(char *s,char *t,char *w)
{
    int count=0;
    int i=0;
    while(s[i]!='\0')
    {
        for(int j=i;j<i+str_len(t);j++)
        {
            if(s[j]==t[j-i]) {
                count++;
               // printf("Matching %c and %c\n", s[j], t[j-i]);
                }
                else count=0;
        }
        if(count==str_len(t))
        {
            //found a matching substr.
            //char*x=(char*)malloc(sizeof(char)*str_len(w));
            //for(int k=0;k<str_len(w)+i+1;k++)
              //  x[k]=w[k];
              printf("%s", w);
            i+=str_len(t);
        }
        else 
        {
            printf("%c", s[i]);
            i++;
        }
        
            
         /*   if(str_len(t)==str_len(w))
            {
                pr
                
                
                
                for(int k=i;k<str_len(w)+i;k++)
                s[k]=w[k-i];
            i=i+str_len(t);}
            else if(str_len(t)>str_len(w))
            {
                   
            }
            else if(str_len(t)>str_len(w))
            {
                
            }

    }
        printf("%s", s);*/
    }
}

int main()
{
	int l1, l2, l3;
	scanf("%d", &l1);
	char*s1=(char*)malloc(sizeof(char)*l1);
    scanf("%d", &l2);
    char*s2=(char*)malloc(sizeof(char)*l2);
	scanf("%d", &l3);
	char*s3=(char*)malloc(sizeof(char)*l3);
	replace_substring(s1, s2, s3);
	return 0;

}