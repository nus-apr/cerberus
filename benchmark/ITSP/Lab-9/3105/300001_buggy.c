/*numPass=0, numTotal=3
Verdict:WRONG_ANSWER, Visibility:1, Input:"12
Hello World", ExpOutput:"dlroW olleH

", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"14
baL noisruceR", ExpOutput:"Recursion Lab

", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"44
The quick brown fox jumps over the lazy dog", ExpOutput:"god yzal eht revo spmuj xof nworb kciuq ehT

", Output:""
*/
#include <stdio.h>
#include <string.h>

void reverse(char str[],int start, int end){
    if(start>=end)
        return;
    char temp=str[start];
    str[start]=str[end];
    str[end]=str[start];
    reverse(str,start+1,end-1);
}

int main()
{
    int l;
    scanf("%d",&l);
    char str[l+1];
    gets(str);
    reverse(str,0,l-1);
    return 0;
}