/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef
2", ExpOutput:"efabcd", Output:"efabcd"
Verdict:ACCEPTED, Visibility:1, Input:"programming 
11", ExpOutput:"programming", Output:"programming"
Verdict:ACCEPTED, Visibility:1, Input:"hello-@programmer 
5", ExpOutput:"ammerhello-@progr", Output:"ammerhello-@progr"
Verdict:ACCEPTED, Visibility:0, Input:"hellodear 
3", ExpOutput:"earhellod", Output:"earhellod"
Verdict:ACCEPTED, Visibility:0, Input:"progamming 
0", ExpOutput:"progamming", Output:"progamming"
Verdict:ACCEPTED, Visibility:0, Input:"programming
10", ExpOutput:"rogrammingp", Output:"rogrammingp"
Verdict:ACCEPTED, Visibility:0, Input:"programming 
13", ExpOutput:"ngprogrammi", Output:"ngprogrammi"
Verdict:ACCEPTED, Visibility:0, Input:"abcde 
4", ExpOutput:"bcdea", Output:"bcdea"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz 
5", ExpOutput:"abcdz", Output:"abcdz"
*/
#include <stdio.h>
int rotate_string(char[],int n,int z);

int main() {
    char input_arr[100];
    int n , i ,j, count,N ;

        scanf("%s",input_arr);
        scanf("%d",&n);

    for(count=0 ,  j=0 ;input_arr[j]!='\0' ;j++, count++){;} /* this for loop is designed to count the number of input characters in string*/
    N = n%count ;
    rotate_string ( input_arr,N,count);
	return 0;
}
int rotate_string(char x [],int N, int count){
    int i , k ;
    char output_arr [count];
    for( i=0 ; i<=count-N-1; i++){
        output_arr [i+N]= x[i] ;/* since the loop is being rotated by n counts , the i+n posn in output array will be the i posn in input array . this is till the last element of output array is reached , in which case it continues as a cycle . for this i have used another loop which starts from the first element and goes on till the n-1 element .*/
    }
        for(  i=count - N , k=0 ; k<N; k++ ,i++){
             output_arr[k] =  x[i];
        }
    printf("%s",output_arr);
}