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

int check_safe(int arr[8][8])
{
    for(int i=0;i<8;i++)
    {
        for(int j=0;j<8;j++)
        {
            if(arr[i][j]==1)
            {
                for(int k=0;k<8;k++)
                {
                    for(int l=0;l<8;l++)
                    {
                      if((arr[k][l]==1)&&(k!=i||l!=j))
                        {
                            if(k==i)
                            return 1;
                            if(l==j)
                            return 1;
                            if(((i+j)==(k+l))||((i+7-j)==(k+7-l)))
                            return 1;
                        }
                    }
                }
            }
        }
    }
    return 0;
}

int main()
{
    int mat[8][8];
    for(int i=0;i<8;i++)
    {
        for(int j=0;j<8;j++)
        {
            mat[i][j]=0;
        }
    }
    int N,r,c;
    scanf("%d",&N);
    for(int i=0;i<N;i++)
    {
        scanf("%d %d",&r,&c);
        mat[r][c]=1;
    }
    int flag = check_safe(mat);
    if(flag==1)
    printf("no");
    else 
    printf("yes");
	return 0;
}