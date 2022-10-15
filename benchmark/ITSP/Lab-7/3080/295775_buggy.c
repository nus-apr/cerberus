/*numPass=6, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:"NO
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:"YES
"
Verdict:ACCEPTED, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:"NO
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:"NO
"
*/
#include <stdio.h>

char s1[105],s2[105];
char ch;
int c;
int main() {
    
    char ch=' ';
    int ind=0;
    scanf("%s\n",s1);
    scanf("%c\n",&ch);
    scanf("%d\n",&c);
    scanf("%s\n",s2);
    /*
    Testing Print Statements
    printf(s1);
    printf("\n%c",ch);
    printf("\n%d\n",c);
    printf(s2);*/
    
    int condition1=0,condition2=0;
    int n1=0,n2=0;
    
    //getting lengths of both the strings
    while(s1[n1]!='\0')n1++;
    while(s2[n2]!='\0')n2++;
    
    //testing print statement
    //printf("%d %d",n1,n2);
    //checking character condition
   for(int i=0;i<n1&&c>0;i++)
   if(s1[i]==ch)c--;
    
    //if condition is true
    if(c>0)condition1=1;
    
    //checking substring condition
    for(int i=0;i<n1;i++)
    {
    
    if(i+n2<=n1)//if s2 can fit from i onwards
    {
    int posi=1;    
    for(int j=0,k=i;j<n2;j++)
    if(s1[k]!=s2[j]){posi^=1;break;}//changing parity of posi
    
    if(posi){condition2=1;break;}//changing parity of condition2
        
    }
    
    }
    
    if(condition1^condition2)//only 1 correct condition
    printf("YES\n");
    else printf("NO\n");

	return 0;
}