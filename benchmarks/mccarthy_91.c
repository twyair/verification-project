#include "common.h"

int mccarthy_91(int n) {
    freeze(N, n);
    ensures(then(N <= 101, ret == 91, ret == N - 10));
    int c = 1;
    while (c != 0) {
        if (n > 100) {
            n -= 10;
            c--;
        } else {
            n += 11;
            c++;
        }
        assert(
            then(
                N > 100,
                c == 0 && n == N - 10,
                c >= 0
                && n <= 10 * c + 91
                && (n >= 91 || c > 0)
            )
        );
    }
    return n;
}
