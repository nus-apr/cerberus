/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:""
*/
#include <stdio.h>

int check_char(char st[],int l,char c,int num)
{
    int i,count=0;
    for(i=0;i<l;i++)
    {
        if(c==st[i])
        count++;
    }
    
    if(count< num)
    return 1;
    else
    return 0;
}

int length(char s[])
{
    int count=0,i;
    for(i=0;s[i]!='\n';i++)
    {count++;}
    return count;
}

int main()
{
    int n,i; char ch;
    char str[101];
    char sub[101];
    scanf("%s ",str);
    scanf("%c",&ch);
    scanf("%d",&n);
    scanf("%s ",sub);

    int l1=length(str);
    int l2=length(sub);
    int flag2=0;
    
    int flag1=check_char(str,l1,ch,n);
    int j;
    for(i=0;i<l1-l2;i++)
    {
        if(str[i]==sub[0])
        {
            for(j=0;j<l2;j++)
            {
                if(str[i+j]==sub[j])
                flag2=1;
                else 
                flag2=0;
            }
        }
        if(flag2==1)
        break;
    }
    if((flag1 + flag2)==1)
    printf("YES");
    else
    printf("NO");
    return 0;
    
}