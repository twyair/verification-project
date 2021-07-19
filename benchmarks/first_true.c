#include "common.h"

int first_true(bool arr[], int size) {
    requires(size > 0);
    ensures(
        forall(k, range(0, size), then(arr[k] && forall(t, range(0, k), !arr[t]), ret == k))
        && then(forall(k, range(0, size), !arr[k]), ret == size)
    );
    for (int i = 0; i < size; i++) {
        if (arr[i]) {
            return i;
        }
        assert(i >= 0 && forall(k, range(0, i + 1), !arr[k]));
    }
    return size;
}
