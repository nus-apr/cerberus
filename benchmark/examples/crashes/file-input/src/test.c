#include <stdio.h>

int div (int a){
  return 1000 /(a-5);
}

void read_file(char *file_path, char *buf) {
  FILE *fp = fopen(file_path, "r");
  fread(buf, sizeof(int), 1, fp);
  fclose(fp);
}

int main(int argc, char *argv[]) {
  int res, y;
  char buffer[10];
  read_file(argv[1], &buffer);
  int x = buffer[0] - 65;
  printf("%d\n", x);
  y = x - 1;
  res = div(y);
  return 0;
}
