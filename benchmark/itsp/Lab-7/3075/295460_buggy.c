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
13", ExpOutput:"ngprogrammi", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"abcde 
4", ExpOutput:"bcdea", Output:"bcdea"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz 
5", ExpOutput:"abcdz", Output:"abcdz"
*/
#include <stdio.h>

int main()
{
    char string[100],ch;
    int i,j,k,n;
    scanf("%s",&string);
    scanf("%d",&n);
    char rotated_string[100];
    for(i=0;n+i<100;i++)
    {
        rotated_string[n+i]=string[i];
        if(string[i]=='\0')
        {
            break;
        }
    }
    rotated_string[i]='\0';
    for(k=0;k<n;k++)
    {
        rotated_string[k]=string[i-n+k];
    }
    printf("%s",rotated_string);
	return 0;
}