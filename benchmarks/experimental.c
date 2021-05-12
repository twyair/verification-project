#include "common.h"

// taken from [https://github.com/dafny-lang/dafny/blob/master/Test/dafny2/Classics.dfy]
// FIXME:
void additive_factorial(int n, int results[]) {
    requires(n >= 0);
    ensures(results[0] == 1 && forall(k, range(1, n), results[k] == k * results[k - 1]));
    results[0] = 1;
    int u = 1;
    int r = 1;
    while (r < n) {
        remember(1 <= r && r <= n && forall(k, range(1, r), results[k] == k * results[k - 1]));
        assert(0 == 0);
        int v = u;
        int s = 1;
        while (s <= r - 1) {
            u = u + v;
            s = s + 1;
            assert(1 <= s && s <= r && u == s * results[r - 1]);
        }
        results[r] = u;
        r = r + 1;
    }
}
