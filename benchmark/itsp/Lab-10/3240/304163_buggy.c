/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
abc
4
dbca", ExpOutput:"1", Output:"0 aa1 bb1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
abce
4
dbca", ExpOutput:"2", Output:"1 aa1 bb2"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
4
dbca", ExpOutput:"7", Output:"5 aa2 bb7"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
7
balmmmm", ExpOutput:"6", Output:"3 aa3 bb6"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
7
balmaex", ExpOutput:"0", Output:"0 aa0 bb0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
balmaexam", ExpOutput:"2", Output:"0 aa2 bb2"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
pqrstuvwp", ExpOutput:"16", Output:"7 aa9 bb16"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
hellohi
9
lhoeidear", ExpOutput:"6", Output:"2 aa4 bb6"
*/
#include <stdio.h>
#include <stdlib.h>

int makeEqual(char * s1, int n1, char * s2, int n2)
{char *t1,*t2;
t1=(char*)malloc((n1+1)*sizeof(char));
t2=(char*)malloc((n2+1)*sizeof(char));
int g,h;
for(g=0;g<n1;g++)
t1[g]=s1[g];
for(g=0;g<n2;g++)
t2[g]=s2[g];
int i,j,k=0,l=0,count=0;
for(i=0;i<n1;i++)
{
count=0;
for(j=0;j<n2;j++)
{
    if(s1[i]==t2[j])
    {t2[j]=0;
        count=1;
        break;
    }
 }
 if(count==1)
 continue;
 else
 if(count==0)
 k++;
}
printf("%d aa",k);
for(i=0;i<n2;i++)
{
count=0;
for(j=0;j<n1;j++)
{
    if(s2[i]==t1[j])
    {t1[j]=0;
        count=1;
        break;
    }
 }
 if(count==1)
 continue;
 else
 if(count==0)
 l++;
}
printf("%d bb",l);
return(k+l);
    
}

int main(){
int n1,n2,i,j;
char *a,*b;
scanf("%d\n",&n1);
a=(char*)malloc((n1+1)*sizeof(char));
for( i=0;i<n1;i++)
scanf("%c",(a+i));
a[i]='\0';
scanf("\n");
scanf("%d\n",&n2);
b=(char*)malloc((n2+1)*sizeof(char));
for( j=0;j<n2;j++)
scanf("%c",(b+j));
b[j]='\0';
scanf("\n");
//printf("%s\n",a);
//printf("%s",b);
printf("%d",makeEqual(a,n1,b,n2));
free(a);
free(b);
    return 0;
}