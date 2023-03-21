#include <stdio.h>

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int res = 0, y;
  y = x - 1;
  res = 1000 / y;
  printf("%d\n",res);
  return 0;
}
