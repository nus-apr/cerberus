/*numPass=6, numTotal=8
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
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 5
3 2 3 4 5
1 2 3 4 5
6 7 8 9 10
11 23 5 5 5
-1 2 3 4 5", ExpOutput:"1 2 1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:0, Input:"5 2
1 0
0 1
0 0
1 0
0 1", ExpOutput:"2 1 1
", Output:"2 1 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 1
1", ExpOutput:"1 1 1
", Output:"0 -1 -1"
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
int m,n,M[100][100];
int check_im(int k,int i,int j)  //checks for identity
{       int x,y;                        //matrix of order k
    for(x=0;x<k;x++)
    {
      for(y=0;y<k;y++)
       {
           
        if((x==y)&&(M[x+i][y+j]!=1))
           return 0;
        else
         if((x!=y)&&(M[x+i][y+j]!=0))
            return 0;
       }
    }
    return 1;
}


int main()
{   int i,j,mg;
    scanf("%d%d\n",&m,&n);
    for(i=0;i<m;i++)    //reading the elements of the array
    {
    for(j=0;j<n;j++)
    {
      scanf("%d",&M[i][j]);
    }
      scanf("\n");
    }
   if(m>n)//mg stores the maximum possible goodness vale
     mg=n;
   else
     mg=m;
   int c,i1=-1,j1=-1,goodness=0,k=2;
   while(k<=mg)
   {                //checking for identity matix of order k
       c=0;
       for(i=0;m-i>=k;i++)
       {
           for(j=0;n-j>=k;j++)
           {
               c=check_im(k,i,j);
               if(c==1)
               break;
           }
             if(c==1)
               break;
       }
       
      if(c==1)
      {
          goodness=k;
          i1=i+1;
          j1=j+1;
      }
      k++;
   }
     printf("%d %d %d",goodness,i1,j1);
    return 0;
}