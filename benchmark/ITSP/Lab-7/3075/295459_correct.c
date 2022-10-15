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

int main() {
    int n,count=0,i,s,s1;
    char str[100];
	scanf("%s",str);
	scanf("%d",&n);
	count = 0;
	while(str[count] != '\0')
	    count++;
    n = n % count;
    for(int i = 0; i < count; i++){
        if(i - n < 0)
            printf("%c", str[count + (i - n)]);
        else
            printf("%c", str[(i - n)]);
    }
    return 0;
}