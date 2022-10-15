/*numPass=3, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 4 5", ExpOutput:"1111
1  1
1  1
1  1
1111
", Output:"11111
1   1
1   1
11111
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5 6", ExpOutput:"22222
2   2
2   2
2   2
2   2
22222
", Output:"222222
2    2
2    2
2    2
222222
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9 6 7", ExpOutput:"999999
9    9
9    9
9    9
9    9
9    9
999999
", Output:"9999999
9     9
9     9
9     9
9     9
9999999
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 4 5", ExpOutput:"3333
3  3
3  3
3  3
3333
", Output:"33333
3   3
3   3
33333
"
Verdict:ACCEPTED, Visibility:1, Input:"2 2 2", ExpOutput:"22
22
", Output:"22
22
"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 3", ExpOutput:"333
3 3
333
", Output:"333
3 3
333
"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1", ExpOutput:"1
", Output:"1
"
*/
#include<stdio.h>

int main(){
 int n,w,h,x,y;
 scanf("%d %d %d",&n,&w,&h);
 for(x=w;x>=1;x--){
     for(y=h;y>=1;y--){
         if(x==1 || y==1 || x==w || y==h)
          printf("%d",n);
      else{
         printf(" ");
     }
     }
     printf("\n");
 }
	return 0;
}