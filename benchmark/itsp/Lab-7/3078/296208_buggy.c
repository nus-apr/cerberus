/*numPass=1, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"x"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"j"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zb|bx"
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"x"
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rrdrxr"
*/
#include <stdio.h>

void read_string(char A[]){
    int i,j;
    char c;
    i=0;
    scanf("%c",&c);
    while(i<100){
        A[i] = c;
        scanf("%c",&c);
        if(c==A[i]){j=i;break;}
        i++;
    }
    for(i=0;i<=j;i++){
        A[i] = A[i] + A[i]-'a'+1;
        printf("%c",A[i]);
    }
    
}

int main() {
    char s[100];
    read_string(s);
    
	return 0;
}