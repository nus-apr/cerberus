#include <stdio.h>

int division (int a){
  int result;
  if (a > 0)
    result = 1000 / (a - 5);
  else
    result = 1000 / (a + 5);
  return result;
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
  int x = buffer[0];
  printf("%d\n", x);
  if (x > 65){
    y = x - 66;
  } else {
    y = x + 1;
  }
  res = division(y);
  return 0;
}
