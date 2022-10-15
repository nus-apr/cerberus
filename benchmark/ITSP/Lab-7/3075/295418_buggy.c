/*numPass=8, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef
2", ExpOutput:"efabcd", Output:"efabcd"
Verdict:ACCEPTED, Visibility:1, Input:"programming 
11", ExpOutput:"programming", Output:"programming"
Verdict:ACCEPTED, Visibility:1, Input:"hello-@programmer 
5", ExpOutput:"ammerhello-@progr", Output:"ammerhello-@progr"
Verdict:ACCEPTED, Visibility:0, Input:"hellodear 
3", ExpOutput:"earhellod", Output:"earhellod"
Verdict:ACCEPTED, Visibility:0, Input:"progamming 
0", ExpOutput:"progamming", Output:"progamming"
Verdict:ACCEPTED, Visibility:0, Input:"programming
10", ExpOutput:"rogrammingp", Output:"rogrammingp"
Verdict:WRONG_ANSWER, Visibility:0, Input:"programming 
13", ExpOutput:"ngprogrammi", Output:"programming"
Verdict:ACCEPTED, Visibility:0, Input:"abcde 
4", ExpOutput:"bcdea", Output:"bcdea"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz 
5", ExpOutput:"abcdz", Output:"abcdz"
*/
#include <stdio.h>
void rotate(char str[],int n)
{
 int i,count=0,t=0;
 for(i=0;str[i]!='\0';i++)
 {
     count++;
 }
 char rotated[count];
for(i=0;i<count;i++)
{
    if(i+n>=count)
    {
        rotated[t]=str[i];
        t++;
    }
    else
    {
        rotated[i+n]=str[i];
    }
}
for(i=0;i<count;i++)
{
    printf("%c",rotated[i]);
}
}
int main() {
 char str[100];
 scanf("%s",str);
 int n;
 scanf("%d",&n);
 rotate(str,n);
	return 0;
}