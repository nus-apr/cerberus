/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"12
Hello World", ExpOutput:"dlroW olleH

", Output:"@xolleH
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"14
baL noisruceR", ExpOutput:"Recursion Lab

", Output:"@xLab
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"44
The quick brown fox jumps over the lazy dog", ExpOutput:"god yzal eht revo spmuj xof nworb kciuq ehT

", Output:"@x@@w%(ehT
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"65
esuoh sybstaG rof yaw edam dah taht seert eht seert dehsinav stI", ExpOutput:"Its vanished trees the trees that had made way for Gatsbys house

", Output:"@w@Ahouse
"
*/
#include <stdio.h>
#include <string.h>
int length , d ;
 int i = 0 ;
 char new_string[];
void reverse_string(char str[],char new_string[]);

int main()
{
 scanf("%d",&length);
  d = length ;
 char str[length];
 char new_string[length];
 //gets(str);
 scanf("%[^ ]",str);
 reverse_string(str,new_string);
 new_string[d]='\0';
 printf("%s",new_string);
 return 0;
}
void reverse_string(char str[],char new_string[] ){
     if (length==0){
       // printf("%s",new_string);
         return;}
     new_string[i] = str[length-1] ;
     printf("%c",new_string[i]);
     ++i ;
     --length ;
     reverse_string( str,new_string);
     
}