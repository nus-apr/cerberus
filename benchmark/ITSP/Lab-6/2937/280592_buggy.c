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
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"2
1 2
3
12 31 45
", ExpOutput:"1
2
12
31
45
", Output:""
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
", Output:""
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
", Output:""
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
", Output:""
*/
#include <stdio.h>
int ascending()
{
    int x,y,c1,c2;
   scanf("%d\n",&x);
   int array1[x];
    
    for(c1=0;c1<x;c1++)
    {
        scanf("%d ",&array1[c1]);
    }
    
   scanf("%d\n",&y);
   int array2[y];
    
    for(c2=0;c2<y;c2++)
    {
        scanf("%d ",&array2[c2]);
    }
    
    int i1,i2,k;
    i1=0;
    i2=0;
    k=0;
    while(i1<x&&i2<y)
    {
        if(array1[i1]<=array2[i2]){
            printf("%d\n",array1[i1]);
        
            i1++;
        }else{
            printf("%d\n",array2[i2]);
            i2=i2+1;  
        }
    }
    return 0;
}    


int main() {
	
int ascending();
	return 0;
}