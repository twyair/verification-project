#include "common.h"

int partition(int arr[], int size, int sep) {
    requires(size > 0);
    freeze(ARR, arr);
    // specification is still incomplete (e.g. ARR=[0,0,1], arr=[0,1, 1])
    ensures(
        forall(t, range(0, ret), arr[t] < sep)
        && forall(t, range(ret, size), arr[t] >= sep)
        && forall(t, range(0, size), exists(k, range(0, size), arr[k] == ARR[t]))
    );

    int first = 0;
    remember(size > 0 && first >= 0);
    for (; first < size && arr[first] < sep; first++) {
        assert(
            first < size
            && forall(k, range(0, first + 1), arr[k] < sep)
            && forall(t, range(0, size), exists(k, range(0, size), arr[k] == ARR[t]))
        );
    }
    if (first == size) {
        return size;
    }

    for (int i = first + 1; i < size; i++) {
        assert(
            i > first
            && i < size
            && forall(t, range(0, first), arr[t] < sep)
            && forall(t, range(first, i), arr[t] >= sep)
            && forall(t, range(0, size), exists(k, range(0, size), arr[k] == ARR[t]))
        );
        if (arr[i] < sep) {
            int tmp = arr[i];
            arr[i] = arr[first];
            arr[first] = tmp;
            first++;
        }

    }
    return first;
}
