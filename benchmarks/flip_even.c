#include "common.h"

int flip_even(bool arr[], int size) {
    requires(size > 0);
    freeze(ARR, arr);
    ensures(
        forall(k, range(0, size),
            then(
                k % 2 == 0,
                arr[k] == !ARR[k],
                arr[k] == ARR[k]
            )
        )
    );
    for (int i = 0; i < size; i++) {
        if (i % 2 == 0) {
            arr[i] = !arr[i];
        }
        assert(
            i >= 0
            && forall(k, range(0, i + 1), then(k % 2 == 0, arr[k] == !ARR[k]))
            && forall(k, range(i+1, size), arr[k] == ARR[k])
            && forall(k, range(0, size), then(k % 2 == 1, arr[k] == ARR[k]))
        );
    }
}
