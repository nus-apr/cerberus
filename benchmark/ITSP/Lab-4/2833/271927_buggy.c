/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangle is 13"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangle is 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangle is 7"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangle is 22"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangle is 50"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangle is 3"
*/
#include<stdio.h>

int main()
{
int i,j,k, N,count=0;
scanf ( "%d",&N);/*input variable*/
for( i=1;i<=N;i=i+1)
{for (j=1 ; j<=i ; j=j+1)
{for (k=1;k<=j; k=k+1)
{if ((j+k>i) && (k+i>j)&& (i+j>k))/*tiangle inequality*/
count++;}
}
}
printf ("Number of possible triangle is %d", count);
    return 0;
}