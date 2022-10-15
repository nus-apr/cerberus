/*numPass=7, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"3 4
0 1 1 0
1 0 0 1
1 0 2 3", ExpOutput:"2 1 3
", Output:"2 1 3"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 0 1 0
0 0 0 0 1", ExpOutput:"5 1 1
", Output:"5 1 1"
Verdict:ACCEPTED, Visibility:1, Input:"2 2
0 2
3 4", ExpOutput:"0 -1 -1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:1, Input:"1 1
0", ExpOutput:"0 -1 -1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
3 2 3 4 5
1 2 3 4 5
6 7 8 9 10
11 23 5 5 5
-1 2 3 4 5", ExpOutput:"1 2 1
", Output:"1 2 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5 2
1 0
0 1
0 0
1 0
0 1", ExpOutput:"2 1 1
", Output:"2 4 1"
Verdict:ACCEPTED, Visibility:0, Input:"1 1
1", ExpOutput:"1 1 1
", Output:"1 1 1"
Verdict:ACCEPTED, Visibility:0, Input:"10 10
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
0 1 0 0 0 0 0 0 0 0
0 0 1 0 0 0 0 0 0 0", ExpOutput:"3 8 1
", Output:"3 8 1"
*/
#include <stdio.h>

void check_good(int a[][30], int m,int n);//function to print goodness and top corner index. 

int main()
{
    int ar[30][30],m,n; //m rows ,n columns.
    scanf("%d%d",&m,&n);
    int i,j;
    if(m<=30&&n<=30) //as matrix constraints are not given.
    {
     for(i=0;i<m;++i) //input the matrix.
      {
         for(j=0;j<n;++j)
          scanf("%d",&ar[i][j]);
      }
     check_good(ar,m,n); //funct call.
    }
    else 
     printf("too big matrix");
    return 0;
}

void check_good(int a[][30], int m,int n)
{
    int i1,j1,i2,j2,i3=m-1,j3=n-1,size,flag,flag2;//(i1,j1) store the index of the top left corner of square sub-matrix that I'm about to check(whether it is an identity matrix or not) and size stores its dimension.
    //I vary the size from min(m,n) to 1.
    //(i3,j3) store the index to output.
    
     
         for(size=((m<n)?m:n);size>=1;--size)//fixing the size of the                                           sub-matrix.
          {
              flag2=0;
              for(i1=0;i1<=m-size;++i1)//fixing the top left row index                                    of sub-matrix.
               {
                   for(j1=0;j1<=n-size;++j1)//fixing top left column                                      index of sub-matrix.
                    {
                        flag=1;// assuming it to be an identity matrix.
                        for(i2=i1;i2<i1+size;++i2)//going about the                          elements of the sub-matrix to be checked.
                         {
                             for(j2=j1;j2<j1+size;++j2)
                              {
                                  if((i2-i1==j2-j1)&&a[i2][j2]!=1)                             //checking diagnal elements.
                                   {
                                       flag=0;
                                       break;
                                   }
                                  if((i2-i1!=j2-j1)&&a[i2][j2]!=0)                           //checking the non-diagnal elements.
                                   {
                                       flag=0;
                                       break;
                                   }
                              }
                             if (!flag)//don't check other rows of sub                             -matrix if this row doesn't satisfy.
                              {
                                  break;
                              }
                         }
                        if(flag)//if an identity matrix is found.
                         {
                             flag2=1;//so that I don't check for                                 smaller size matrix.
                             if((i1<i2)||((i1==i2)&&(j1<j2))) //updating the final index to be printed acc. to given criteria.
                              {
                                  i3=i1;
                                  j3=j1;
                                  
                              }
                             
                         }
                    }
               }
              if(flag2)//prevent from checking smaller size matrix if                          an identity matrix found.
               break;
          }
     
     if (!flag2)//if no identity matrix is found.
      {
          printf("0 -1 -1");
      }
     else
      printf("%d %d %d",size,i3+1,j3+1);
}