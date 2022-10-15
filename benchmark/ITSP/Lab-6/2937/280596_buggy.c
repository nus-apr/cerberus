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
", Output:"1
1
1
2
2
2
3
5
5
3
5
9
3
5
16
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2
1 2
3
12 31 45
", ExpOutput:"1
2
12
31
45
", Output:"1
1
1
2
2
2
"
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
", Output:"1
2
2
2
2
1
3
4
4
4
1
3
5
6
6
1
3
5
7
8
1
3
5
7
9
"
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
", Output:"-1
-1
-1
-1
1
2
2
2
1
3
5
5
"
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
", Output:"-1
0
-1
0
-1
0
-1
0
-1
0
"
*/
#include <stdio.h>

int min(int a, int b){
    if(a<b){
        return a;
    }
    else{
        return b;
    }
}

int main() {
	
	int n1;
    scanf("%d", &n1);
	int a[n1];
	int i;
	for(i=0; i<n1; i++){
	    scanf("%d", &a[i]);
	}
	int n2;
    scanf("%d", &n2);
	int b[n2];
	int j;
	for(j=0; j<n2; j++){
	    scanf("%d", &b[j]);
	}
	
	for(i=0; i<n1; i++){
	    for(j=0; j<n2; j++){
	        printf("%d\n", min(a[i], b[j]));
	    }
	}
	
	
	
	
	return 0;
}