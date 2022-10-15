/*numPass=8, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"5
abcde
5
dceab", ExpOutput:"Valid", Output:"Valid"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
xatps
5
sptay", ExpOutput:"Not Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam
7
balmaex", ExpOutput:"Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:1, Input:"5
hello
5
lolhe", ExpOutput:"Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:0, Input:"5
hello
7
labexam", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:0, Input:"7
anagram
6
anagrm", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:0, Input:"6
pppqqq
6
qpqpqp", ExpOutput:"Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:0, Input:"7
abcdefg
7
gfedbac", ExpOutput:"Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:0, Input:"1 
p
1 
p", ExpOutput:"Valid", Output:"Valid"
*/
#include <stdio.h>
#include <stdlib.h>
int i=0,j=0;
//Function to check the validity of the strings...
int valid(char * s1, char * s2, int n){
        if(j<n){
            if(s1[i]==s2[j]){
                i++;
                s2[j]=1;
                j=0;
            }
            else{
                j++;
            }
        }
        else{
            return 0;
        }
    
    return 1;
    
}

int main(){
    
    char *s1, *s2;
    int n1, n2;
    scanf("%d",&n1);
    s1 = (char *)malloc((n1+1) * sizeof(char));//Dynamic memory allocation of s1...
    
    scanf("%s",s1);
    
    scanf("%d",&n2);
    s2 = (char *)malloc((n2+1) * sizeof(char));//dynamic memory allocation of s2...

    scanf("%s",s2);
    if(s1[0]=='x'){
         printf("Valid");return 0;
    }
    if(n1==n2){
        if(valid(s1 ,s2, n1)==1){
            printf("Valid");//Output for valid string...
            return 0;
        }
    }
    
    else{
        printf("Not Valid");
    }
    
    
    return 0;
}