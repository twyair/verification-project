#include "common.h"

// taken from [https://github.com/dafny-lang/dafny/blob/master/Test/dafny2/Classics.dfy]
int additive_factorial(int n) {
    requires(n >= 0);
    phantom(int results[]);
    ensures(results[n] == ret && forall(k, range(1, n + 1), results[k] == k * results[k - 1]) && results[0] == 1);
    phantom(results[0] = 1);
    int u = 1;
    int r = 1;
    while (r <= n) {
        remember(1 <= r && r <= n && forall(k, range(1, r), results[k] == k * results[k - 1]) && results[0] == 1);
        int v = u;
        assert(results[r - 1] == v && v == u);
        int s = 1;
        while (s <= r - 1) {
            u = u + v;
            s = s + 1;
            assert(1 <= s && s <= r && u == s * results[r - 1]  && results[r - 1] == v);
        }
        phantom(results[r] = u);
        r = r + 1;
    }
    return u;
}
