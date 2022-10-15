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
int k=0;
 int check_palindrome(char str[],int index,int l){;
     if(index>l){
         return 0;
     }
     if(str[index]==str[l-1]){k=k+1;}
        else k=0;
         check_palindrome(str,index+1,l-1);
      return k;
    
 }
int main()
{
   char str[100];
   scanf("%s",str);
   int index=0;
   int l=strlen(str);
   int r=check_palindrome(str,index,l);//printf("%d",r);
   if(r==l/2+l%2){
     printf("Yes");
   }
  else printf("No");/* Use Recursion to solve the problem*/   
    return 0;
}