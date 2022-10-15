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
int checksum(int arr[],int size,int sum){
    if(sum==0){
        return 1;
    } else {
        checksum(array,n-1,sum-array[n-1]);
    }
    
}
int areSplitsEqual(int sum,int len, int sum_split_A)
{
    if(sum%2==0){
    if(checksum(array,n,sum/2)){
        return 1;
    } else {
        return 0;
    }
} else {
    return 0;
}
    
    
}

int main()
{
scanf("%d",&n);
int i=0;
while(i<n){
    scanf("%d",&array[i]);
    i=i+1;
}
   int sum=0;
   int j=0;
   while(j<n){
       sum=sum+array[j];
       j=j+1;
   }// read n;
	// read n elements into array

	printf("%s\n", areSplitsEqual(sum,0, 0)==1?"YES":"NO");
}