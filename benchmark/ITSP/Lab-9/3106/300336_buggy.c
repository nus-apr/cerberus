/*numPass=2, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"liril", ExpOutput:"Yes
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"oolaleloo", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"sorewaslerelsaweros", ExpOutput:"Yes
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"qwertyuiiuytrpwq", ExpOutput:"No
", Output:"No"
*/
#include <stdio.h>
#include <string.h>
int palin(char s[],int n){
    
    if (n==0)return 1;
    else if (s!=s+n)return 0;
    else return palin(s+1,n-1);
}
 
int main(){
    char s[100];
    int n,z;
    scanf("%s",s);
    n=strlen(s);
    z=palin(s,n);
    if (z==1){
        printf("Yes");
    }
    else if(z==0){
        printf("No");
    }
    return 0;
}