/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4 hehe
6 hehehe", ExpOutput:"he", Output:"he"
Verdict:ACCEPTED, Visibility:1, Input:"4 abab
8 abababab", ExpOutput:"abab", Output:"abab"
Verdict:ACCEPTED, Visibility:1, Input:"4 heeh
6 hehehe", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"5 hello
6 hihihi", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1 a
5 aaaaa", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
#include <stdlib.h>

// Write auxillary functions here

int main(){

    char *s1, *s2;
    int len1, len2, i, j=0, k=0;
    scanf("%d ",&len1);
    s1=(char*)malloc(sizeof(char)*len1);
    scanf("%s",s1);
    scanf("%d",&len2);
    s2=(char*)malloc(sizeof(char)*len2);
    scanf("%s",s2);
    for(i=0;i<len1;i++)
    {
        if(s1[i]==s2[i])
        {
            j=j+1;
        }
        else if(s1[i]!=s2[i])
        {
            break;
        }
    }
     if((len2%j)==0 && j==len1)
    {
        printf("%s",s1);
    }
    else if((len2%j)!=0 && j==len1)
    {
        for(i=j;i<len2;i++)
        {
            if(s1[i-j]==s2[j])
            {
                k=k+1;
            }    
        }
        for(i=0;i<(k+1);i++)
        {
            printf("%c",s1[i]);
        }
    }
	return 0 ; 
}