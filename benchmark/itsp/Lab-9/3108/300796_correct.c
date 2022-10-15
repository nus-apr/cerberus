/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
7 3 8 2 6", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:1, Input:"5
7 3 8 1 6", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:1, Input:"10
1 2 3 4 5 6 7 8 9 10", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"20
5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 95", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"20
100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 38 100 54 76 134", ExpOutput:"YES
", Output:"YES
"
Verdict:ACCEPTED, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 80", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"19
1 2 3 4 5 6 7 8 9 10 18 17 16 15 14 13 12 11 99", ExpOutput:"YES
", Output:"YES
"
*/
#include <stdio.h>

int n, array[20]; // n won't be more than 20

int areSplitsEqual(int len, int sum_split_A, int sum_split_B)
{    
    if(n==0||n==1){return 0;}
    if(n>1){                              //write the base case
        int i,sum=0;
        for(i=0;i<n;i++){
        sum=sum+array[i];                 //to split the array into two parts,sum of all 
        }                                 //elements of the array should be divisible by 2
        if(sum%2!=0){return 0;}        
    }                                 
     int idx,rdx;
     if(len<n){
         idx=areSplitsEqual(len+1,sum_split_A+array[n-len],sum_split_B);
         rdx=areSplitsEqual(len+1,sum_split_A,sum_split_B+array[n-len]);
         if(idx==1||rdx==1){
             return 1;
         }
         else{
             return 0;
         }
     }else return 1;
     

}
int main()
{
    int i;                               // read n;
    scanf("%d\n",&n);
    for(i=0;i<n;i++){
        scanf("%d ",&array[i]);
    }                                   //read n elements into array

	printf("%s\n", areSplitsEqual(0, 0, 0)==1?"YES":"NO");
}