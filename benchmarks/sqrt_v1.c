#include "common.h"

int sqrt_v1(int num) {
    requires(num > 0);
    // FIXME? doesnt work with `, ret == -1)`
    ensures(then(exists(k, range(1, num), k * k == num), ret * ret == num));
    for (int i = 1; i < num; i++) {
        if (i * i == num) {
            return i;
        }
        assert(i >= 1 && forall(k, range(0, i+1), k * k != num));
    }
    return -1;
}
