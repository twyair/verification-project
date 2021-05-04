#include "common.h"

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

void vector_add(int v[], int u[], int res[], int size) {
    requires(size > 0);
    for(int i = 0; i < size; i += 1) {
        res[i] = v[i] + u[i];
        assert(forall(k, range(0, i + 1), res[k] == v[k] + u[k]));
    }
    assert(forall(k, range(0, size), res[k] == v[k] + u[k]));
}

bool is_prime(int num) {
    requires(num > 1);
    remember(num >= 2);
    ensures(forall(k, range(2, num), num % k != 0) == ret);
    for (int i = 2; i != num; i += 1) {
        if (num % i == 0) {
            return 0 != 0;
        }
        assert(i >= 2 && i < num && forall(k, range(2, i + 1), num % k != 0));
    }
    return 0 == 0;
}

/* takes the root of a perfect square
 * the result for a non-perfect square is `-1`
 */
int sqrt_v1(int num) {
    requires(num > 0);
    ensures(then(exists(k, range(1, num), k * k == num), ret * ret == num)); // doesnt work with `, ret == -1)`
    for (int i = 1; i < num; i += 1) {
        if (i * i == num) {
            return i;
        }
        assert(i * i != num && i >= 1 && forall(k, range(0, i+1), k * k != num));
    }
    return -1;
}