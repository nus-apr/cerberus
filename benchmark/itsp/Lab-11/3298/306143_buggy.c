/*numPass=3, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 4 5", ExpOutput:"0
1 2 3 4 5 
", Output:"0
1 2 3 4 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
5 4 3 2 1", ExpOutput:"10
1 2 3 4 5 
", Output:"12
1 2 3 4 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 3 2 1", ExpOutput:"3
1 1 2 3 
", Output:"5
1 1 2 3 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"100
49	28	45	49	61	14	82	12	44	52	43	61	9	74	89	44	47	25	28	80	23	95	17	69	49	54	38	77	10	47	14	65	21	48	84	16	40	66	40	16	84	88	76	10	22	27	100	41	71	77	57	52	83	97	54	42	30	96	56	65	95	39	44	35	59	48	11	45	62	94	12	51	58	17	87	10	46	59	78	21	74	84	50	40	87	50	68	55	53	1	48	30	37	16	42	10	47	40	32	40", ExpOutput:"2497
1 9 10 10 10 10 11 12 12 14 14 16 16 16 17 17 21 21 22 23 25 27 28 28 30 30 32 35 37 38 39 40 40 40 40 40 41 42 42 43 44 44 44 45 45 46 47 47 47 48 48 48 49 49 49 50 50 51 52 52 53 54 54 55 56 57 58 59 59 61 61 62 65 65 66 68 69 71 74 74 76 77 77 78 80 82 83 84 84 84 87 87 88 89 94 95 95 96 97 100 
", Output:"343
1 9 10 10 10 10 11 12 12 14 14 16 16 16 17 17 21 21 22 23 25 27 28 28 30 30 32 35 37 38 39 40 40 40 40 40 41 42 42 43 44 44 44 45 45 46 47 47 47 48 48 48 49 49 49 50 50 51 52 52 53 54 54 55 56 57 58 59 59 61 61 62 65 65 66 68 69 71 74 74 76 77 77 78 80 82 83 84 84 84 87 87 88 89 94 95 95 96 97 100 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"100
57	67	48	54	70	64	47	23	33	67	21	68	13	51	96	94	92	100	12	42	11	32	51	61	24	100	26	23	6	93	34	26	42	49	39	53	72	79	42	69	19	55	63	48	91	52	99	30	73	99	48	99	53	95	58	3	3	69	56	56	49	34	1	96	32	6	16	11	13	83	31	43	20	100	33	39	65	89	17	15	18	62	12	56	42	48	61	99	54	5	97	24	100	38	58	96	45	29	36	12", ExpOutput:"2584
1 3 3 5 6 6 11 11 12 12 12 13 13 15 16 17 18 19 20 21 23 23 24 24 26 26 29 30 31 32 32 33 33 34 34 36 38 39 39 42 42 42 42 43 45 47 48 48 48 48 49 49 51 51 52 53 53 54 54 55 56 56 56 57 58 58 61 61 62 63 64 65 67 67 68 69 69 70 72 73 79 83 89 91 92 93 94 95 96 96 96 97 99 99 99 99 100 100 100 100 
", Output:"328
1 3 3 5 6 6 11 11 12 12 12 13 13 15 16 17 18 19 20 21 23 23 24 24 26 26 29 30 31 32 32 33 33 34 34 36 38 39 39 42 42 42 42 43 45 47 48 48 48 48 49 49 51 51 52 53 53 54 54 55 56 56 56 57 58 58 61 61 62 63 64 65 67 67 68 69 69 70 72 73 79 83 89 91 92 93 94 95 96 96 96 97 99 99 99 99 100 100 100 100 "
Verdict:ACCEPTED, Visibility:0, Input:"1
42", ExpOutput:"0
42 
", Output:"0
42 "
Verdict:ACCEPTED, Visibility:0, Input:"2
2 2", ExpOutput:"0
2 2 
", Output:"0
2 2 "
*/
#include <stdio.h>
#include <stdlib.h>
int i;
int rA=0,rB=0,r=0;
int merge(int ar[],int start,int n){
    int temp[n],k,i=start,j=start+n/2;
    int lim_i=start+n/2,lim_j=start+n;
    for(k=0;k<n;k++){
        if((i<lim_i)&&(j<lim_j)){    //both active
            if(ar[i]<=ar[j]){
                temp[k]=ar[i];
                i++;
            }
        
            else{
               temp[k]=ar[j];
               rA++;
               j++;
            }
        }
    else if(i==lim_i){         //1st half done
        temp[k]=ar[j];     //copy 2nd half
        j++;
    }  
        else{  //2nd half done
        temp[k]=ar[i];      //copy 1st half
        r++;
        i++;
    }
    }
    for(k=0;k<n;k++){
        ar[start+k]=temp[k];   //in place
    }
}

void merge_sort(int ar[],int start,int n){
    if(n>1){
        int half=n/2;
        merge_sort(ar,start, half);
        merge_sort(ar,start+half,n-half);
        merge(ar,start,n);
    }
}
int main(){
    int n;
    scanf("%d\n",&n);
    int* ar;
    ar=(int*)malloc(n*sizeof(int));
    for(i=0;i<n;i++){
        scanf("%d ",&ar[i]);
    }
    merge_sort(ar,0,n);
    printf("%d\n",rA+rB+r);
    for(i=0;i<n;i++){
        printf("%d ",ar[i]);
    }
    return 0;
}