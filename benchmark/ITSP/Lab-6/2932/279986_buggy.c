/*numPass=6, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"10"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"19457"
Verdict:ACCEPTED, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"-1365"
Verdict:ACCEPTED, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"8"
Verdict:ACCEPTED, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"55312397"
Verdict:ACCEPTED, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:"-341"
*/
#include <stdio.h>
void input(int [],int );//this is the prototype for input() which will input and store values in array b[]
void assign(int [],int [],int );//this is prototype for assign which will store values in a[]
void input(int c[],int size){
    int i;
     for(i=0;i<size;i++)
      scanf("%d ",&c[i]);
}
void assign(int e[],int f[],int m){
    int i=0,j;
     while(i<m)
      {e[i]=f[i];
       i++;
      }
     while(i<=30)
      { e[i]=0;
        for(j=1;j<=m;j++)
         e[i]+=e[i-j];
        i++;
      }     
} 
int main() {
  int d,N,b[20],a[30];//size of a[] is 30 because in output we have to print a[N] where N will be <=30.
   scanf("%d %d",&d,&N);
    input(b,N);
	 assign(a,b,d);
   printf("%d",a[N]);	  
	return 0;
}