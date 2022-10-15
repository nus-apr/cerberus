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
int palin(char s[],int t,int n){
    
    if (n==0)return 1;
    else if (s[t]!=s[n-1])return 0;
    else return palin(s,t+1,n-1);
}
 
int main(){
    char s[100];
    int n,z,t=0;
    scanf("%s",s);
    n=strlen(s);
    z=palin(s,t,n);
    if (z==1){
        printf("Yes");
    }
    else if(z==0){
        printf("No");
    }
    return 0;
}