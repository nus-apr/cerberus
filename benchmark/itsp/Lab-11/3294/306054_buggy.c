/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2-32"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"201510505101520"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4-14"
Verdict:WRONG_ANSWER, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"161161-4161116"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8", ExpOutput:"8 3 -2 3 8 ", Output:"83-238"
*/
#include <stdio.h>
int n;
void res(int i){
    if(i<=0){printf("%d",i);
    return;
    
}
 printf("%d",i);
 res(i-5);
 printf("%d",i);
}
int main(){
scanf("%d",&n);
res(n);
	return 0;
}