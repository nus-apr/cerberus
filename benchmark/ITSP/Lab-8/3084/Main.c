/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for nontrivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
-----------------------------------------------------------------------------------------------------------

A queen in a chessboard can attack another queen if it is placed in the same row/same column/same diagonal. Given the number of queens and their position (row,col) on the chessboard, find out if it is a safe arrangement or not. An arrangement is said to be safe if no queen can attack another queen. Print "yes" if it is a safe arrangement and "no" if there is atleast one queen who can attack another.

Constraints:
The chessboard size is 8x8.

Input:
An integer N, which denotes the number of queens on board.
Following it are N lines having two integers R and C, denoting the row number and column number.
They are indexed from 0.

Output:
yes (if it is a safe arrangement)
no (if it is not a safe arrangement)
*/
#include <stdio.h>
#include <string.h>

int main()
{
    int mat[8][8];
    int r,c,n;
    memset(mat,0,sizeof(mat));
    scanf("%d",&n);
    int row[8],col[8],diag1[16],diag2[16];
    memset(row,0,sizeof(row));
    memset(col,0,sizeof(col));
    memset(diag1,0,sizeof(diag1));
    memset(diag2,0,sizeof(diag2));
    int found=0;
    for(int i=0;i<n;i++)
    {
        scanf("%d %d",&r,&c);
        mat[r][c]=1;
        if(row[r]==1)found=1;
        else row[r]=1;
        if(col[c]==1)found=1;
        else col[c]=1;
        if(diag1[r+c]==1)found=1;
        else diag1[r+c]=1;
        if(diag2[8+r-c]==1)found=1;
        else diag2[8+r-c]=1;
    }
    if(found==1)
        printf("no\n");
    else
        printf("yes\n");
        
    return 0;
}