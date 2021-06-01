#include <string.h>
#include <stdio.h>

struct sty {
    int f1;
    int f2;
};

struct bbb {
    struct sty y;
};

struct aaa {
    struct bbb *x;
};

struct sty s;
struct aaa *c;

int foo(struct sty **p) {
    p[0]->f1 ++;
    return s.f2;
}

int main(int argc, char** argv) {
    if (argc < 2) return 0;
    FILE *f = fopen(argv[1], "r");
    struct sty *p[1];
    memset(&c->x->y, 0, sizeof(struct sty));
    c->x->y.f2 = 10;
    p[0] = &s;
    if (f == NULL) return 0;
    fscanf(f, "%d", &s.f2);
    fclose(f);
    printf("%d\n", foo(p));
    return 0;
}
