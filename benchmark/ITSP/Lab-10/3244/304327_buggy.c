/*numPass=4, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
abcde", ExpOutput:"Good String", Output:"Not Good String"
Verdict:WRONG_ANSWER, Visibility:1, Input:"8
pqrsabcd", ExpOutput:"Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:1, Input:"4
azpg", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
aaaazzzz", ExpOutput:"Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"6
abczpq", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"6
abcpqz", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
acegikmo", ExpOutput:"Good String", Output:"Not Good String"
Verdict:WRONG_ANSWER, Visibility:0, Input:"ab", ExpOutput:"Good String", Output:"Not Good String"
*/
#include <stdio.h>
#include <stdlib.h>
int mod(char a,char b){
    if(a<b)return b-a;
    else if(a>=b)return a-b; 
    
}

int main(){
    char *s,*r;
    int n;
    scanf("%d",&n);
    s = (char*)malloc((n+1)*sizeof(char)); 
    r = (char*)malloc((n+1)*sizeof(char));
    scanf("%s",s);
    
    int i;
    for(i=0;i<n;i++){
        *(r+i)=*(s+n-i-1);
    }
    int x;
    for(i=1;i++;i<n){
        if(mod(*(s+i),*(s+i-1))==mod(*(r+i),*(r+i-1))){
            x=1;
            continue;
        }
        else{
            x=0;
            break;
        }
        
        
    } 
    if(x==1)printf("Good String");
    else if(x==0)printf("Not Good String");
    
    
    
    
    
    
    return 0;
}