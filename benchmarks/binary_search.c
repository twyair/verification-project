#include "common.h"

int binary_search(int arr[], int size, int key) {
    requires(
        size > 0
        && forall(k, range(0, size - 1), arr[k] <= arr[k + 1])
    );
    ensures(then(
        exists(k, range(0, size), arr[k] == key),
        arr[ret] == key && ret < size && ret >= 0,
        ret == -1
    ));
#ifdef ANNOTATIONS
    {
        remember(
            forall(k, range(0, size - 1), arr[k] <= arr[k + 1])
        );
        for (int i = 0; i < size; i++) {
            for (int j = i; j >= 0; j--) {
                assert(
                    forall(k, range(0, i), forall(t, range(0, k + 1), arr[t] <= arr[k]))
                    && forall(t, range(j, i + 1), arr[t] <= arr[i])
                    && i < size && i >= 0
                    && j >= 0 && j <= i
                );
            }
            assert(
                forall(k, range(0, i + 1), forall(t, range(0, k + 1), arr[t] <= arr[k]))
                && i < size && i >= 0
            );
        }
    }
#endif
    remember(
        forall(k, range(0, size), forall(t, range(0, k + 1), arr[t] <= arr[k]))
    );
    int lo = 0;
    int hi = size;
    while (lo < hi) {
        assert(
            lo >= 0
            && hi > lo
            && hi <= size
            && forall(k, range(0, lo), arr[k] < key)
            && forall(k, range(hi, size), arr[k] > key)
        );
        int mid = (lo + hi) / 2;
        if (key < arr[mid]) {
            hi = mid;
        } else if (arr[mid] < key) {
            lo = mid + 1;
        } else {
            return mid;
        }
    }
    return -1;
}
