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
/*fuction to check 3 conditions    *
 *1.their rows should not be same  *
 *2.Their columns must not be same *
 *3.the diff between their row and * 
 *column of both should not be same*/
int mod(int a)
{
    int b=(a>0)?a:-a;
    return b;
}
int checkit( int mat[][2],int n)
{
    int i=0;
    while(i<n-1)
    {
        int j=i+1;
        while(j<n)
        {
            
            if (mat[i][1]==mat[j][1]) return 0;
            if (mat[i][0]==mat[j][0]) return 0;
            if(mod(mat[i][0]-mat[j][0])==mod(mat[i][1]-mat[j][1])) return 0;
            j++;
        }
        i++;
    }
    return 1;
}
//to read the values
void read(int mat[][2],int n)
{
    int i=0,j;
    for(i=0;i<n;i++)
    {
        for(j=0;j<2;j++)
        scanf("%d",&mat[i][j]);
    }
}
int main() {
    int n,mat[70][2];
	scanf("%d",&n);
	read(mat,n);
	if(checkit(mat,n)) printf("yes");
	else printf("no");
	return 0;
}