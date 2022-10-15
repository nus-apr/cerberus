/*numPass=3, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"3
1 0 0 
0 1 0 
0 0 1", ExpOutput:"1", Output:"1
"
Verdict:ACCEPTED, Visibility:1, Input:"3
1 2 3 
4 5 6
7 8 9", ExpOutput:"0", Output:"0
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1
1", ExpOutput:"1", Output:"0
"
Verdict:ACCEPTED, Visibility:0, Input:"2
1 2 
4 3", ExpOutput:"-5", Output:"-5
"
*/
#include <stdio.h>
#include <stdlib.h>


//power function
int powe(int base,int exp1)
{
    if(exp1%2==0)return 1;
    
    return -1;
}

int Determinant(int *matrix,int n)
{
    
    //base case
    if(n==2)
    {
    return matrix[0]*matrix[3]-matrix[2]*matrix[1];
    }
  
    int j=0,k=0;
    int ret=0;
    
    /*for(int i=0;i<n;i++)
    {
        for(int l=0;l<n;l++)
         printf("%d ",matrix[i*n+l]);
         printf("\n");
    }*/
    for(k=0;k<n;k++)
    {
    int ind=0;    
    int *m2=(int*)malloc((n-1)*(n-1)*sizeof(int));    
    
    for(int i=0;i<n;i++)
    for(int l=0;l<n;l++)
    if(i==j||l==k)continue;
    else m2[ind++]=matrix[i*n+l];
    //Testing print statements
    //printf("%d %d\n",j,k);
    /*for(int i=0;i<n-1;i++)
    {
        for(int l=0;l<n-1;l++)
        printf("%d ",m2[i*(n-1)+l]);
        printf("\n");
    }*/
    
    //prinf(powe(-1,j+k))
   
    //recursive step
    ret+=matrix[j*n+k]*powe(-1,j+k)*Determinant(m2,n-1);
    
    }
    //return determinant uptil now
    return ret;
}

int *matri;
int n1;
int main(){
    //declaration and input
    scanf("%d",&n1);
    
    matri=(int*)malloc((n1)*(n1)*sizeof(int));
    // printf("%d",sizeof(matrix)/sizeof(int));
     for(int i=0;i<n1;i++)
     for(int j=0;j<n1;j++)
     scanf("%d",&matri[i*n1+j]);
    
    /*for(int i=0;i<n;i++)
    {for(int j=0;j<n;j++)
    
	printf("%d ",matrix[i*n+j]);
    printf("\n");
    }*/
    printf("%d\n",Determinant(matri,n1));
    return 0;
}