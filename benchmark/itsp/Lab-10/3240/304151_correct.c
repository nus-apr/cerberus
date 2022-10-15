/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"3
abc
4
dbca", ExpOutput:"1", Output:"1"
Verdict:ACCEPTED, Visibility:1, Input:"4
abce
4
dbca", ExpOutput:"2", Output:"2"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam
4
dbca", ExpOutput:"7", Output:"7"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam
7
balmmmm", ExpOutput:"6", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam
7
balmaex", ExpOutput:"0", Output:"0"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam
9
balmaexam", ExpOutput:"2", Output:"2"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam
9
pqrstuvwp", ExpOutput:"16", Output:"16"
Verdict:ACCEPTED, Visibility:0, Input:"7
hellohi
9
lhoeidear", ExpOutput:"6", Output:"6"
*/
#include <stdio.h>
#include <stdlib.h>
int n1,n2,count=0;
int get_common_elements(char *str1,char *str2) {
    int i,j;
    for (i=0;i<n1;i++) {
        for (j=0;j<n2;j++) {
            if (str1[i]==str2[j]) {
                count++;
               str1[i]=1;str2[j]=2; 
            }
        }
    }
    return count;
}
int makeEqual(char * str1, int n1, char * str2, int n2){
    int k=get_common_elements(str1,str2);
    return n1+n2-2*k;//return the total no of elements(n1+n2) subtracted by total common elements.
}

int main(){
    char *str1,*str2;int result;
    scanf("%d",&n1);    //read size of first string
    str1=(char *)malloc((n1+1)*sizeof(char));//dynamic memory alloc.
    scanf("%s",str1);   //read first string
    scanf("%d",&n2);    //read size of second string
    str2=(char *)malloc((n2+1)*sizeof(char));//dynamic memory alloc.
    scanf("%s",str2);   //read second string
    result=makeEqual(str1,n1,str2,n2);
    printf("%d",result);
    return 0;
}