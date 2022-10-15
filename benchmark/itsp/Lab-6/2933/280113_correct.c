/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14
2
13 42", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:1, Input:"6
1 2 3 4 5 6
3
3 2 1", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 3 6 1
2
1 6", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 3 5 7 9
2
2 4", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"5
9 9 8 9 9
2
9 9", ExpOutput:"YES
", Output:"YES
"
*/
#include <stdio.h>
void input(int [],int );//this is prototype for input() which will input and store values in the array
int check(int [],int [],int ,int );//prototype for check() which will return 1 if A2 is a contiguous subarray of A1,else it will return -1
void input(int a[],int size){
  int i=0;
   while(i<size)
     {scanf("%d",&a[i]);
      i++;
     } 
}
int check(int a[],int b[],int s1,int s2){
   int i,j,count,k;
    for(i=0;i<s1;i++)
     { 
         if(a[i]==b[0])
           {  k=i;
               count=0;
                for(j=1;j<s2;j++)
                 { if(b[j]==a[++k])
                   count++;
                 }
              if(count==s2-1)
               return 1;
           }
     }
return 0; 
}    
int main() {
  int N1,A1[20],N2,A2[20],b;
   scanf("%d",&N1);
    input(A1,N1);
   scanf("%d",&N2);
    input(A2,N2);
   b=check(A1,A2,N1,N2);//b will store the value 1 if A2 is a contiguous subarray,else it will store 0	
    if(b==1)
     printf("YES\n");
    else 
     printf("NO\n");
	return 0;
}