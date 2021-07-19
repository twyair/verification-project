#include "common.h"

int sqrt_v2(int num) {
    requires(num > 0);
    ensures(ret * ret <= num && (ret + 1) * (ret + 1) > num);
    int i = 1;
    while (i * i <= num) {
        assert(i >= 1 && i <= num && forall(k, range(0, i + 1), k * k <= num));
        i++;
    }
    return i - 1;
}
