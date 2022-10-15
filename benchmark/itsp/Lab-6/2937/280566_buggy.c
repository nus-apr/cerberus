/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 2 5 9 16
3
3 5 21", ExpOutput:"1
2
3
5
5
9
16
21
", Output:"1/n2/n3/n5/n5/n9/n16/n21/n"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2
1 2
3
12 31 45
", ExpOutput:"1
2
12
31
45
", Output:"1/n2/n12/n31/n45/n"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
2 4 6 8 10
5
1 3 5 7 9", ExpOutput:"1
2
3
4
5
6
7
8
9
10
", Output:"1/n2/n3/n4/n5/n6/n7/n8/n9/n10/n"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
-1 2 5
4
1 3 7 9", ExpOutput:"-1
1
2
3
5
7
9
", Output:"-1/n1/n2/n3/n5/n7/n9/n"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 2 3 4 5
2
-1 0", ExpOutput:"-1
0
1
2
3
4
5
", Output:"-1/n0/n1/n2/n3/n4/n5/n"
*/
#include <stdio.h>

void array_value(int t[],int n){//to initialise the array
    for(int i=0;i<n;i++){
        scanf("%d",&t[i]);
    }
}
int main(){
	int n,m;
	scanf("%d",&n);
	int A[n];
	array_value(A,n);
	scanf("%d",&m);
	int B[m],C[m+n];
    array_value(B,m);
    for(int i=0;i<(m+n);i++){
        if(i<n)
            C[i]=A[i];
        else
            C[i]=B[i-n];
    }
    for(int i=0;i<(m+n);i++){
        for(int j=i+1;j<(m+n);j++){
            if(C[i]>C[j]){
                int swap=C[i];
                C[i]=C[j];
                C[j]=swap;
            }
        }
    }
    for(int i=0;i<(m+n);i++)
        printf("%d/n",C[i]);
	return 0;
}