/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"5
abcde", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:1, Input:"8
pqrsabcd", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:1, Input:"4
azpg", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"8
aaaazzzz", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:0, Input:"6
abczpq", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"6
abcpqz", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"8
acegikmo", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:0, Input:"ab", ExpOutput:"Good String", Output:"Good String"
*/
#include <stdio.h>
#include <stdlib.h>

int main(){
    char *str;
    int count=0;//counts no. of times condition is true
    int len,i;
    
    scanf("%d\n",&len);
    str=(char*)malloc((len+1)*sizeof(char));//dynamic allocation
    scanf("%s",str);
    str[len]='\0';
    
    if(len>1)
    { for(i=1;i<len;i++)
      { if((str[i]-str[i-1])==(str[len-i]-str[len-i-1]))
        {
            count++;
        }
        
       else if((str[i]-str[i-1])==(str[len-i-1]-str[len-i]))
        {
          count++;
        }
        
      }
    
    
    if(count==len-1) 
    {printf("Good String");}
    
    else
    {printf("Not Good String");}
    
    }
    
    else if(len==1||len==0)
    {printf("Good String");}
    
    
    
    
    free(str);//free the space
    return 0;
}