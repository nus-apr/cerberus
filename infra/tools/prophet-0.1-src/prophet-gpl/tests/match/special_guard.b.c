int foo(int a, int b) {
    return a/b;
}

int main() {
    int a = 10;
    int b = 0;
    if ((b != 0) && foo(a, b))
        return 1;
    return 0;
}
