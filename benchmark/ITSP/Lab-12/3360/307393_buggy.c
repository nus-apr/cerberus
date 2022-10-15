/*numPass=3, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4
1 100 99 100
2 100 98 98
3 1 1 1
4 91 12 12", ExpOutput:"1
2
4
3
", Output:"1
2
4
3
"
Verdict:ACCEPTED, Visibility:1, Input:"3
13745 30 59 50
12845 31 23 50
12424 31 23 40
", ExpOutput:"12845
13745
12424
", Output:"12845
13745
12424
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 50 20 30
4 30 40 10
2 40 40 10
3 35 29 40", ExpOutput:"3
1
2
4
", Output:"1
2
3
4
"
Verdict:ACCEPTED, Visibility:0, Input:"2
1 50 50 50
2 50 30 50", ExpOutput:"1
2
", Output:"1
2
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4
1 50 50 50
2 50 30 50
3 20 50 56 
4 58 29 50", ExpOutput:"3
4
1
2
", Output:"1
3
4
2
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 50 50 30
2 20 30 50
3 80 50 66 
4 10 29 10
5 10 10 10", ExpOutput:"3
2
1
4
5
", Output:"2
3
1
4
5
"
*/
#include <stdio.h>
#include <stdlib.h>

typedef struct student Std;

struct student{ int roll,phy,chm,mth;};

Std *ar;

void rearrange(int n)
{
    int i,j;
    int t1,t2,t3,t4;
    for(i=0;i<n;i++)
    {
        for(j=0;j<n-1;j++)
        {
        
           if(ar[i+1].mth > ar[i].mth)
           {
               t1=ar[i+1].roll;
               ar[i+1].roll=ar[i].roll;
               ar[i].roll=t1;
               
               t2=ar[i+1].phy;
               ar[i+1].phy=ar[i].phy;
               ar[i].phy=t2;
               
               t3=ar[i+1].chm;
               ar[i+1].chm=ar[i].chm;
               ar[i].chm=t3;
               
               t4=ar[i+1].mth;
               ar[i+1].mth=ar[i].mth;
               ar[i].mth=t4;
           }
        
        else if(ar[i+1].mth ==ar[i].mth)
        {
            if(ar[i+1].phy>ar[i].phy)
            {
                t1=ar[i+1].roll;
               ar[i+1].roll=ar[i].roll;
               ar[i].roll=t1;
               
               t2=ar[i+1].phy;
               ar[i+1].phy=ar[i].phy;
               ar[i].phy=t2;
               
               t3=ar[i+1].chm;
               ar[i+1].chm=ar[i].chm;
               ar[i].chm=t3;
               
               t4=ar[i+1].mth;
               ar[i+1].mth=ar[i].mth;
               ar[i].mth=t4;
            } 
            
            else if(ar[i+1].phy==ar[i].phy)
            {
                if(ar[i+1].chm>ar[i].chm)
               {
                     t1=ar[i+1].roll;
                    ar[i+1].roll=ar[i].roll;
                    ar[i].roll=t1;
               
                     t2=ar[i+1].phy;
                    ar[i+1].phy=ar[i].phy;
                     ar[i].phy=t2;
               
                        t3=ar[i+1].chm;
                        ar[i+1].chm=ar[i].chm;
                        ar[i].chm=t3;
               
                         t4=ar[i+1].mth;
                        ar[i+1].mth=ar[i].mth;
                        ar[i].mth=t4;
               } 
            }
        }
            
        }
    }
}

int main() 
{
    int n;
    scanf("%d",&n);
    ar = (Std*)malloc(n*sizeof(Std));
    
 for(int i=0;i<n;i++)
 {
 scanf("%d %d %d %d",&ar[i].roll,&ar[i].phy,&ar[i].chm,&ar[i].mth);
 }
    rearrange(n);
    for(int i=0;i<n;i++)
    {
        printf("%d\n",ar[i].roll);
    }
    free (ar);
    return 0;
}