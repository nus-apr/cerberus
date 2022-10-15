/*numPass=3, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 4 5", ExpOutput:"1 2 3 4 5 
", Output:"1 2 3 4 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
5 4 3 2 1", ExpOutput:"1 2 3 4 5 
", Output:"2 4 3 5 1 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 3 2 1", ExpOutput:"1 1 2 3 
", Output:"1 2 3 1 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"100
49	28	45	49	61	14	82	12	44	52	43	61	9	74	89	44	47	25	28	80	23	95	17	69	49	54	38	77	10	47	14	65	21	48	84	16	40	66	40	16	84	88	76	10	22	27	100	41	71	77	57	52	83	97	54	42	30	96	56	65	95	39	44	35	59	48	11	45	62	94	12	51	58	17	87	10	46	59	78	21	74	84	50	40	87	50	68	55	53	1	48	30	37	16	42	10	47	40	32	40", ExpOutput:"1 9 10 10 10 10 11 12 12 14 14 16 16 16 17 17 21 21 22 23 25 27 28 28 30 30 32 35 37 38 39 40 40 40 40 40 41 42 42 43 44 44 44 45 45 46 47 47 47 48 48 48 49 49 49 50 50 51 52 52 53 54 54 55 56 57 58 59 59 61 61 62 65 65 66 68 69 71 74 74 76 77 77 78 80 82 83 84 84 84 87 87 88 89 94 95 95 96 97 100 
", Output:"1 9 10 10 10 12 12 14 10 14 11 16 16 17 17 21 21 22 23 25 27 28 30 30 35 32 37 38 39 40 40 40 40 28 41 16 42 42 40 44 45 44 45 43 46 44 47 47 48 48 49 47 49 48 49 50 52 51 52 50 53 54 54 55 56 57 58 59 61 61 59 62 65 66 71 69 74 74 65 76 77 77 78 80 82 83 68 84 84 87 84 87 88 94 89 95 95 96 97 100 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"100
57	67	48	54	70	64	47	23	33	67	21	68	13	51	96	94	92	100	12	42	11	32	51	61	24	100	26	23	6	93	34	26	42	49	39	53	72	79	42	69	19	55	63	48	91	52	99	30	73	99	48	99	53	95	58	3	3	69	56	56	49	34	1	96	32	6	16	11	13	83	31	43	20	100	33	39	65	89	17	15	18	62	12	56	42	48	61	99	54	5	97	24	100	38	58	96	45	29	36	12", ExpOutput:"1 3 3 5 6 6 11 11 12 12 12 13 13 15 16 17 18 19 20 21 23 23 24 24 26 26 29 30 31 32 32 33 33 34 34 36 38 39 39 42 42 42 42 43 45 47 48 48 48 48 49 49 51 51 52 53 53 54 54 55 56 56 56 57 58 58 61 61 62 63 64 65 67 67 68 69 69 70 72 73 79 83 89 91 92 93 94 95 96 96 96 97 99 99 99 99 100 100 100 100 
", Output:"1 3 3 5 6 6 12 11 12 11 12 13 13 15 16 18 19 20 21 23 23 24 17 26 24 26 31 30 32 29 32 33 33 34 34 38 36 39 42 39 42 42 42 47 45 48 48 48 43 49 48 49 51 51 53 52 54 54 53 55 56 56 56 57 58 61 58 61 62 63 65 67 64 67 69 69 70 72 73 79 89 83 91 93 94 68 95 96 92 96 97 96 99 99 100 100 100 99 100 99 "
Verdict:ACCEPTED, Visibility:0, Input:"1
42", ExpOutput:"42 
", Output:"42 "
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"
", Output:""
*/
#include <stdio.h>
#include<stdlib.h>
void swap(int*arr,int i,int j)
{
    int temp;//swapping the variable
    temp=arr[i];
    arr[i]=arr[j];
    arr[j]=temp;
    
}

int part(int arr[],int n)
{
    int left=0,right=n-1,pivot=arr[0];
    while(left<=n-1 && right>=0)
    {
        while(arr[left]<=pivot && left<right)
        left++;//move towards right
        while(arr[right]>=pivot && left<right)
        right--;//move towards left
        if(left<right)
        {
            swap(arr,left,right);
            left++;
            right--;
        }
        else
        {
            swap(arr,left-1,0);//swapping
            return left-1;
        }
    }
}

void quicksort(int arr[],int n)
{
    int pivndex;//stores the index
    if(n<=1)
    return;
    pivndex=part(arr,n);
    quicksort(arr,pivndex);
    quicksort(arr+pivndex+1,n-pivndex-1);
}

int main()
{
    int i,n,j;
    scanf("%d",&n);
    int*arr;
    arr=(int*)malloc(n*sizeof(int));//dynamically allocating memory
    
    for(i=0;i<n;i++)
    {scanf("%d ",arr+i);}
    
    quicksort(arr,n);//calling quicksort
    
    for(j=0;j<n;j++)
    {
        printf("%d ",arr[j]);
    }
    
    
    return 0;
}