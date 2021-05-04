#include "common.h"

/* takes the root of a perfect square
 * the result for non-perfect squares is undefined
 */
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

// TODO:
void merge(int arr1[], int arr2[], int res[], int size1, int size2) {
    requires(
        size1 > 0 && size2 > 0
        && forall(k, range(0, size1 - 1), arr1[k] <= arr1[k+1])
        && forall(k, range(0, size2 - 1), arr2[k] <= arr2[k+1])
    );
    ensures(forall(k, range(size1 + size2 - 1), res[k] <= res[k+1]));
}