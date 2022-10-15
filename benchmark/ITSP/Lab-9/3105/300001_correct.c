/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"12
Hello World", ExpOutput:"dlroW olleH

", Output:"dlroW olleH"
Verdict:ACCEPTED, Visibility:1, Input:"14
baL noisruceR", ExpOutput:"Recursion Lab

", Output:"Recursion Lab"
Verdict:ACCEPTED, Visibility:0, Input:"44
The quick brown fox jumps over the lazy dog", ExpOutput:"god yzal eht revo spmuj xof nworb kciuq ehT

", Output:"god yzal eht revo spmuj xof nworb kciuq ehT"
Verdict:ACCEPTED, Visibility:0, Input:"65
esuoh sybstaG rof yaw edam dah taht seert eht seert dehsinav stI", ExpOutput:"Its vanished trees the trees that had made way for Gatsbys house

", Output:"Its vanished trees the trees that had made way for Gatsbys house"
*/
#include <stdio.h>
#include <string.h>

void reverse(char str[],int start, int end){
    if(start>=end)
    {
        //whenever start gets greater than end, reversion is complete
        //base case
        return;
    }
    char temp=str[start]; //general steps of swapping 
    str[start]=str[end];
    str[end]=temp;  //temp is temporary variable
    reverse(str,start+1,end-1); //recursive call of function
}

void input(char str[],int key,int size){
    if(key>=size-1)
    {
        //base case, do not exceed size of string
        str[size-1]='\0';
        return;
    }
    str[key]=getchar(); 
    input(str,key+1,size); //recursive step
}

void output(char str[],int key,int size){
    if(key==size-1)
    {
        //base case. do not exceed size of string
        return;
    }
    putchar(str[key]);
    output(str,key+1,size); //recursive step
}


int main() {
    char str[101];
    int l; //to store length of string
    scanf("%d",&l);
    char ch=getchar(); //do surpass the newline character
    input(str,0,l);
    reverse(str,0,l-2);
    output(str,0,l);
    return 0;
}