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

int main()
{
    char string[100],ch;
    int i,j,k,n,l;
    scanf("%s",&string);
    scanf("%d",&n);
    char rotated_string[100];
    int m;
    for(l=0;l<100;l++)
    {
        if(string[l]=='\0')
        {
            break;
        }
    }
    m=n%l;
    for(i=0;m+i<100;i++)
    {
        rotated_string[m+i]=string[i];
        if(string[i]=='\0')
        {
            break;
        }
    }
    rotated_string[i]='\0';
    for(k=0;k<m;k++)
    {
        rotated_string[k]=string[i-m+k];
    }
    printf("%s",rotated_string);
	return 0;
}