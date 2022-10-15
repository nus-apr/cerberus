/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:ACCEPTED, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"tvxz"
Verdict:ACCEPTED, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"zxvt"
Verdict:ACCEPTED, Visibility:1, Input:"t", ExpOutput:"n", Output:"n"
Verdict:ACCEPTED, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xxx"
Verdict:ACCEPTED, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"htjjnx"
Verdict:ACCEPTED, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zbbpbxxxbhhjhnjlnfbljl"
Verdict:ACCEPTED, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"xxxxx"
Verdict:ACCEPTED, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rrlrdrxrnx"
*/
#include <stdio.h>

int main() {
char str[100];
scanf("%s",str);/*scanning input string*/
int i;
int count = 0;
for(i=0;;i++){/*reading length*/
    if(str[i]=='\0'){
        break;
    }
    else{count = count + 1;}
}
for(i=0;i<count;i++){
    if(str[i]-'a'+1<=13){/*if character is below n*/
    str[i]=str[i]-'a'+1+str[i];
    continue;
    }
    else if(str[i]-'a'+1>13){/*if character is above n*/
        str[i]='a'+((str[i]-'a')-('z'-str[i]));
        continue;
    }
    else if(str[i]=='\0')break;/*breaking loop after shifting whole                                     string*/
}
printf("%s",str);

	return 0;
}