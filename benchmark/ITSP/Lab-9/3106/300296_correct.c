/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"liril", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:1, Input:"oolaleloo", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"sorewaslerelsaweros", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:0, Input:"qwertyuiiuytrpwq", ExpOutput:"No
", Output:"No"
*/
#include <stdio.h>
#include <string.h>
int chk_palin(char ar[100], int size, int start, int mid)
{
    if (start==mid)
        return 1;
    if (ar[start]==ar[size-start-1])
        return chk_palin(ar, size, start+1, mid);
    else
        return 0;
    
}
 
int main()
{
    char s[100];
    int n, m;
    scanf ("%s", s);
    n=strlen(s);
    m=chk_palin(s, n, 0, n/2);
    if (m==1)
        printf ("Yes");
    else
        printf ("No");
    return 0;
}