/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 2
3 1 -5
0 -2 4
", ExpOutput:"4
0 -6 10 14 -20 ", Output:"4
0 -6 10 14 -17 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 4
2 -4 4 3 -1 6
1 -2 -5 2 4

", ExpOutput:"9
2 -8 2 19 -27 -15 15 -20 8 24 ", Output:"9
2 -8 2 19 -27 -15 15 -20 8 27 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"15 15 
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"30
1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 ", Output:"30
1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 4632366 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 10
100 100 -200 -300 421 535 125 -235 122 -555 99
100 100 -200 -300 421 535 125 -235 122 -555 99

", ExpOutput:"20
10000 20000 -30000 -100000 64200 311200 53600 -488600 -216359 382870 392475 104480 160299 -454920 -424767 -90160 300484 -181950 332181 -109890 9801 ", Output:"20
10000 20000 -30000 -100000 64200 311200 53600 -488600 -216359 382870 392475 104480 160299 -454920 -424767 -90160 300484 -181950 332181 -109890 9995 "
*/
#include <stdio.h>

int main() {
    int n1=0,n2=0;
    int i,j,k;

    int multiple;

    scanf("%d",&n1);
    scanf("%d",&n2);
        int p1[n1+1];
    int p2[n2+1];
    int arr[n1+n2+1];
        for(k=0;k<n1+n2;k++){
        arr[k]=0;
    }
    for(i=0;i<n1+1;i++)
    {
        scanf("%d",&p1[i]);
    }
    for(j=0;j<n2+1;j++)
    {
        scanf("%d",&p2[j]);
    }
            i=0,j=0;
            while(i<n1+1){
                j=0;
                while(j<n2+1){
                    arr[i+j]+=p1[i]*p2[j];
                    j++;
                }
                i++;
            }
    printf("%d\n",n1+n2);
    for(k=0;k<n1+n2+1;k++){
            printf("%d ",arr[k]);
    }
    return 0;
}