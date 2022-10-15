/*numPass=3, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"3
1 0 0 
0 1 0 
0 0 1", ExpOutput:"1", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
1 2 3 
4 5 6
7 8 9", ExpOutput:"0", Output:"-3"
Verdict:ACCEPTED, Visibility:0, Input:"1
1", ExpOutput:"1", Output:"1"
Verdict:ACCEPTED, Visibility:0, Input:"2
1 2 
4 3", ExpOutput:"-5", Output:"-5"
*/
#include <stdio.h>
#include <stdlib.h>

//function for calculating power of -1.
int  power(int q)
{
    int i,res=1;
    for(i=1;i<=q;i++)
    {
        res=-1*res;
    }
    return res;
}

int Determinant(int **mat,int n,int i,int j)
{
    static int q=-1;
    int sum=0;
//base cases.
    if(n==0)
    {
        return 0;
    }
    else if(n==1)
    {
        return mat[i][j];
    }
    else if(n==2)
    {
        return mat[i][j]*mat[i+1][j+1]-mat[i][j+1]*mat[i+1][j];
    }
//these are the three base cases.
    else
    {
        int s,t,x,y,**new;
        
     
    new=(int**)malloc(n*sizeof(int*));
    int a;
    for(a=0;a<n;a++)
    {
        new[a]=(int*)malloc(n*sizeof(int));
    }
        
        for(s=0;s<n;s++)
        {
            for(x=1;x<n;x++)
            {
                t=0;
                for(y=0;y<n;y++)
                {
                    if(y==s)
                    continue;
                    new[x-1][t]=mat[x][y];
                    t++;
                }
            }
            
  sum=sum+power(++q)*mat[i][j]*Determinant(new,n-1,i,j);
            return sum;
            //using recursion.
        }
    }
    return 0;
}


int main(){
    int n;
    scanf("%d\n",&n);
//making array of arrays.i.e. matrix to store data.
    int **mat;
    mat=(int**)malloc(n*sizeof(int*));
    int i,j;
    
    for(i=0;i<n;i++)
    {
        mat[i]=(int*)malloc(n*sizeof(int));
    }
//scanning the given elemants using pointers.
    for(i=0;i<n;i++)
    {
        for(j=0;j<n;j++)
        {
            scanf("%d ",(*(mat+i)+j));
        }
        scanf("\n");
    }
    
    int res=Determinant(mat,n,0,0);
    printf("%d",res);
//printing the output.
    free(mat);
//freeing the occupied space.
    return 0;
}