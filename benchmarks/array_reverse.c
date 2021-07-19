#include "common.h"

void array_reverse(int arr[], int size) {
    requires(size > 0);
    freeze(ARR, arr);
    ensures(forall(k, range(0, size), ARR[k] == arr[size - 1 - k]));
    for (int i = 0; i < size / 2; i++) {
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
