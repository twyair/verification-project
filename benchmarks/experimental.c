#include "common.h"

// works but takes forever to verify - why?
void vector_add(float v[], float u[], float res[], int size) {
    requires(size > 0);
    for(int i = 0; i < size; i += 1) {
        res[i] = v[i] + u[i];
        assert(forall(k, range(0, i + 1), res[k] == v[k] + u[k]));
    }
    assert(forall(k, range(0, size), res[k] == v[k] + u[k]));
}

// V works
bool is_prime(int num) {
    requires(num > 1);
    remember(num >= 2);
    ensures(forall(k, range(2, num), num % k != 0) == ret);
    for (int i = 2; i < num; i += 1) {
        if (num % i == 0) {
            return 0 != 0;
        }
        assert(i >= 2 && forall(k, range(2, i + 1), num % k != 0));
    }
    return 0 == 0;
}

int sqrt_v1(int num) {
    requires(num > 0);
    // doesn't work
    // ensures(then(exists(k, range(1, num), k * k == num), ret * ret == num, ret == -1));
    ensures(ret * ret == num || ret == -1);
    for (int i = 1; i < num; i += 1) {
        if (i * i == num) {
            return i;
        }
        assert(num > i && i > 0 && forall(k, range(1, i + 1), k * k != num));
    }
    return -1;
}

int sqrt_v2(int num) {
    requires(num > 0);
    ensures(then(exists(k, range(1, num), k * k == num), ret * ret == num));

    int bit = 1;
    while (bit * 4 <= num){
        assert(forall(k, range(1, bit), k * 4 <= num));
        bit *= 4;
    }

    int res = 0;
    while (bit != 0) {
        if (num >= res + bit) {
            num -= res + bit;
            res = res * 2 + bit;
        } else {
            res /= 2;
        }
        bit /= 4;
    }

    return res;
}