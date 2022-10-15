/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"12 -3 2 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"420 15 10 5 0 5 10 15 20 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"14 -1 4 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"416 11 6 1 -4 1 6 11 16 "
*/
#include <stdio.h>
int n,count=0,*array,k;
int get_size(int n) {//function te get size of array in which thw sequence is to be stored.
    if (n<=0) return count;        //base case.
    else {                        //recursive step.
        count++;
        get_size(n-5);
        return count;
    }
}
void fill_pattern(int n,int index) {//fuction to fill the array and print it.
    if ((index==(2*k+1)/2)||n<=0) {
        array[index]=n;
    } 
    else {
        array[index]=n;array[(2*k+1)-1-index]=n;
        fill_pattern(n-5,index+1);
    }
}
int main(){
    int i;
    scanf("%d",&n);
    k=get_size(n);printf("%d",k);
    array=(int *)malloc((2*k+1)*sizeof(int));
    fill_pattern(n,0);
    for (i=0;i<2*k+1;i++) {
        printf("%d ",array[i]);
    }
	return 0;
}