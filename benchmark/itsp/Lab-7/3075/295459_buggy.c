/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef
2", ExpOutput:"efabcd", Output:"ff"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming 
11", ExpOutput:"programming", Output:"gnimmargor"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer 
5", ExpOutput:"ammerhello-@progr", Output:"remmarremm"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear 
3", ExpOutput:"earhellod", Output:"rara"
Verdict:WRONG_ANSWER, Visibility:0, Input:"progamming 
0", ExpOutput:"progamming", Output:"gnimmagor"
Verdict:WRONG_ANSWER, Visibility:0, Input:"programming
10", ExpOutput:"rogrammingp", Output:"gnimmargo"
Verdict:WRONG_ANSWER, Visibility:0, Input:"programming 
13", ExpOutput:"ngprogrammi", Output:"gnimmag"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcde 
4", ExpOutput:"bcdea", Output:"edc"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz 
5", ExpOutput:"abcdz", Output:"zdcb"
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
        if(i + n < count)
            printf("%c", str[count - i + n]);
        else
            printf("%c", str[count - (i + n)%count]);
    }
    return 0;
}