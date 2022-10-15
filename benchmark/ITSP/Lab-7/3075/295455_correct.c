/*numPass=9, numTotal=9
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
Verdict:ACCEPTED, Visibility:0, Input:"programming 
13", ExpOutput:"ngprogrammi", Output:"ngprogrammi"
Verdict:ACCEPTED, Visibility:0, Input:"abcde 
4", ExpOutput:"bcdea", Output:"bcdea"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz 
5", ExpOutput:"abcdz", Output:"abcdz"
*/
#include <stdio.h>

int rotate(char str[], int n, int count)
{
    int i, j;
    for(i=0; i<=n; i++)
    {
        for(j=(count+1); j>=0; j--)
        {
            str[j] = str[j-1];
        }
        str[0] = str[count+1];
        str[count+1]='\0';
    }
    return 0;
}

int main() 
{
    int n, i, count;
    char str[101];
    for(i=0; i<101; i++)
    {
        str[i]='\0';
    }
    scanf("%s\n%d", str, &n);
    for(i=0, count=0; (i<100) && (str[i]!='\0'); i++)
    {
        count+=1;
    }
    if(n>count)
    {
        n = n%(count);
    }
    rotate(str, n, count);
    for(i=0; i<(count+1); i++)
    {
        printf("%c", str[i]);
    }
	return 0;
}