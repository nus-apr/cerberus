/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:"0 0NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:"1 1NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:"0 1YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:"0 1YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:"0 1YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:"0 1YES"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:"1 1NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:"0 1YES"
*/
#include <stdio.h>


int compare(char a1[],char a2[],int num,int j)
{
    int r=0;
    for(int k=j;k<num+j;k++)
    {
        if(a1[k]!=a2[r++])
        return 0;
    }
    return 1;
}



int main() 
{
    int n=0;
    char ch=0;
    char s1[101];
    char s2[101];
    int count=0;
    int i=0;
    int l=0;
    int c=0;
    int flag1=0;
    int flag2=0;
    int m=0;
      scanf("%s\n",s1);
      scanf("%c\n",&ch);
      scanf("%d\n",&n);
      scanf("%s",s2);
      while(s2[m++]!='\0')
      l++;
     /* c=getchar();
          while((c!=EOF)&&(c!='\n'))
          {
             s2[l++]=c;
             c=getchar();
          }
       s2[l]='\0';*/
           while(s1[i]!='\0')
           {
              if(ch==s1[i++])
              count++;
           }
    if(count<n)
    {
      flag1=1;
    }
          for(int j=0;j<i;j++)
          {
            if((s1[j]==s2[0])&&(i-j>=l))
            {
             flag2=compare(s1,s2,l,j);
             if(flag2==1)
             break;
            }
          }
          
          printf("%d %d",flag1 ,flag2);
    if(flag1==flag2)
    printf("NO");
    
    if(flag1!=flag2)
    printf("YES");
    
    
	return 0;
}