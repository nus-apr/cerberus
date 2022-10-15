/*numPass=4, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefgh"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"NNNN"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdz
265", ExpOutput:"fghie", Output:"fghiR"
Verdict:WRONG_ANSWER, Visibility:1, Input:"pou
2605", ExpOutput:"utz", Output:"utR"
Verdict:ACCEPTED, Visibility:0, Input:"a
0", ExpOutput:"a", Output:"a"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abab
25", ExpOutput:"zaza", Output:"zzzz"
Verdict:ACCEPTED, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
26", ExpOutput:"thisproblemhasnoautomatedtestcases", Output:"thisproblemhasnoautomatedtestcases"
Verdict:ACCEPTED, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
27", ExpOutput:"uijtqspcmfnibtopbvupnbufeuftudbtft", Output:"uijtqspcmfnibtopbvupnbufeuftudbtft"
*/
#include <stdio.h>
int count_arr(char[],int);
int main() {
char a[100];
scanf("%s", a);
int i,n,t;
scanf("%d", &n);
t=count_arr(a,100);
if(n>=26)
{
    n=n%26;
}
for(i=0;i<t;i++)
{
    if(a[i]+n>='z')
    {
        a[i]='a';
        a[i]=a[i]+n-('z'-a[i]);
    }
    a[i]=a[i]+n;
}
for(i=0;i<t;i++)
{
    printf("%c", a[i]);
}
return 0;
}
int count_arr(char x[],int size) {
    int i,count=0;
    for(i=0;i<size&&(x[i]!='\n'&&x[i]!='\0');i++)
    {
        count++;
    }
    return count;
}