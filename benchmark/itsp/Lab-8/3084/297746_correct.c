/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"3
1 1
2 3
4 5", ExpOutput:"no
", Output:"no"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 1
2 3
4 6
7 0", ExpOutput:"yes
", Output:"yes"
Verdict:ACCEPTED, Visibility:0, Input:"4
0 0
4 5
5 4
3 6", ExpOutput:"no
", Output:"no"
Verdict:ACCEPTED, Visibility:0, Input:"4
1 2
5 4
4 7
0 0", ExpOutput:"yes
", Output:"yes"
*/
#include <stdio.h>

int main() {
	int i,N,j;
	scanf("%d",&N);
	int r[N],c[N];/*two arrays which will store the values of       rows and columns */
	for(i=0;i<N;i++){
	    scanf("%d%d",&r[i],&c[i]);
	}
	int p=0;
	for(i=0;i<N;i++){
	    for(j=0;j<N;j++){
	        /*condition for unsafe arrangement */
	        if(i!=j&&(r[i]==r[j]||c[i]==c[j]||(r[i]-r[j])==(c[i]             -c[j])||(r[i]-r[j])==-(c[i]-c[j]))){
	            p=1;/*to check that this condition has once been                 true*/  
	        }
	        else continue;
	    }
	}
	if(p==0){
	    printf("yes");
	}
	else{
	    printf("no");
	}
	return 0;
}