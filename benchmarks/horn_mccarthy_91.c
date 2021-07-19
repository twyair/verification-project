#include "common.h"

int mccarthy_91(int n) {
    freeze(N, n);
    ensures(then(N <= 101, ret == 91, ret == N - 10));
    int c = 1;
    while (c != 0) {
        if (n > 100) {
            n -= 10;
            c -= 1;
        } else {
            n += 11;
            c += 1;
        }
    }
    return n;
}