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

 int pal(char s[],int start,int end){
     if(start>=end){return 1;}
 if(s[start]==s[end]){
   return  pal(s,start+1,end-1);
 }else{
     return 0;
 }
     
     
 }
int main()
{
    char s[100];
    scanf("%s",s);
    int n=strlen(s);
  
 
    if(pal(s,0,n-1)){
        printf("Yes");
    }else{
        printf("No");
    }
    return 0;
}