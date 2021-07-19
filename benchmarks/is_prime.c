#include "common.h"

bool is_prime(int num) {
    requires(num > 1);
    remember(num > 1);
    ensures(forall(k, range(2, num), num % k != 0) == ret);
    for (int i = 2; i != num; i++) {
        if (num % i == 0) {
            return false;
        }
        assert(i >= 2 && i < num && forall(k, range(2, i + 1), num % k != 0));
    }
    return true;
}
