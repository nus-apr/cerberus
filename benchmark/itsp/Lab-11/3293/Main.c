/*
--------------------------------------------
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0 marks. 
---------------------------------------------

The problem is to colour the countries of the world in such a way that the countries which are adjacent to each other are painted in different colours.

Given the input C, the countries are denoted by the numbers {0,1…,C-1}. You are also given a (2-dimensional matrix or) graph G with the dimensions CxC where G[i,j] is 1 if Country i is adjacent to Country j, else G[i,j] is 0. The number of colours is given by m. Your output should be a line giving the colours, in which the respective countries {0,1,….,C-1} are painted, separated by a space. 

Assume that you will always have enough number of colours to paint all the countries in the desired manner.

HINT: Start by colouring the 0th country with 1. To colour the i-th country, look at the i-th row of G and check the countries from 0 to i-1 which are adjacent to i. Then give the i-th country the least colour from 1 to m which can be used.

NOTE: Always start by colouring the 0th country with 1 and then increment the colour number as required. Otherwise, you may get a different solution than the one which will be accepted.

Example:  Input (C followed by G and m respectively):

4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0
3

Output

1 2 3 2
*/
#include <stdio.h>
#include <stdlib.h>

void printSolution(int solution[],int C){
	for(int i=0;i<C;i++)
		printf("%d ",solution[i]);
}

int isSafe(int ver,int col,int solution[],int **graph){
	for(int i=0;i<ver;i++){
		if(graph[ver][i] && col==solution[i])
			return 0;
	}
	return 1;

}

int graphColoring(int ver,int** graph,int m , int solution[],int C){
	if(ver==C)
		return 1;
	for(int col=1;col<=m;col++){
			if(isSafe(ver,col,solution,graph)){
				solution[ver] = col;
				if(graphColoring(ver+1,graph,m,solution,C))
					return 1;
				else
					solution[ver] = 0;
			}
	}
	return 0;

}

int main(){
	int C;
	scanf("%d",&C);
	
	int **G = (int **)malloc(C * sizeof(int **));
	for(int i=0;i<C;i++){
		G[i] = (int*)malloc(C*sizeof(int*));
	}

	for(int i=0;i<C;i++){
		for(int j=0;j<C;j++){
			scanf("%d",&G[i][j]);
		}
	}

	int m;
	scanf("%d",&m);

    int solution[C];

    for(int i=0;i<C;i++)
    	solution[i]=0;
    graphColoring (0,G,m,solution,C);
   	printSolution(solution,C);

	return 0;
}