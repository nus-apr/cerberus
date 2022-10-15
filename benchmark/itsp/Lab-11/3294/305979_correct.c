/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2 -3 2 "
Verdict:ACCEPTED, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"20 15 10 5 0 5 10 15 20 "
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4 -1 4 "
Verdict:ACCEPTED, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"16 11 6 1 -4 1 6 11 16 "
Verdict:ACCEPTED, Visibility:0, Input:"8", ExpOutput:"8 3 -2 3 8 ", Output:"8 3 -2 3 8 "
*/
#include <stdio.h>
int i,j;
int fun_two(j){
    printf("%d ",j);
    if(j<=0)
    return fun_one(j);
    else
    return fun_two(j-5);
}
int fun_one(i){
    printf("%d ",i+5);
    if((i+5)!=j)
    return fun_one(i+5);
}

int main(){
    scanf("%d",&j);
    fun_two(j);
	return 0;
}