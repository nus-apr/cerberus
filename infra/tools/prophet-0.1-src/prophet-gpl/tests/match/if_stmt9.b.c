struct sty2 {
    int y;
    int z;
};

struct sty {
    int x;
    struct sty2 *p;
};

int main() {
    struct sty s;
    if (s.x > 0 && s.p != 0 && s.p->z == 0 && s.p->y == 1)
        return -1;
    return 0;
}
