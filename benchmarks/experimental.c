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

/* takes the root of a perfect square
 * the result for a non-perfect square is `-1`
 */
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

// works
void array_reverse(int arr[], int size) {
    requires(size > 0);
    freeze(ARR, arr);
    ensures(forall(k, range(0, size), ARR[k] == arr[size - 1 - k]));
    for (int i = 0; i < size / 2; i += 1) {
        int tmp = arr[i];
        arr[i] = arr[size - 1 - i];
        arr[size - 1 - i] = tmp;
        assert(
            size > 0
            && i >= 0
            && forall(k, range(0, i + 1), arr[k] == ARR[size - 1 - k] && arr[size - 1 - k] == ARR[k])
            && forall(k, range(i + 1, (size + 1) / 2), arr[k] == ARR[k] && arr[size - 1 - k] == ARR[size - 1 - k])
        );
    }
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