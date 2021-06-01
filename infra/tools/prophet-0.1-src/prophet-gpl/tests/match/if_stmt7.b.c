struct sty {
    int x;
    int y;
    int z;
};

int main() {
    struct sty s;
    if (s.x > 0 && (s.y == 0 && s.z == 1))
        return -1;
    return 0;
}
