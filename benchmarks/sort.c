#include "common.h"

void bubble_sort(int arr[], int size) {
    requires(size > 0);
    ensures(forall(k, range(0, size - 1), arr[k] <= arr[k + 1]));
    for (int j = 0; j < size; j += 1) {
        for (int i = 0; i != size - j - 1; i += 1) {
            if (arr[i] > arr[i + 1]) {
                int tmp = arr[i + 1];
                arr[i + 1] = arr[i];
                arr[i] = tmp;
            }
            assert(
                forall(k, range(0, i + 1), arr[k] <= arr[i + 1])
                && forall(
                    k, range(size - j, size),
                    forall(t, range(0, k), arr[t] <= arr[k])
                )
                && i >= 0
                && i < size - j - 1
            );
        }
        assert(
            forall(
                k, range(size - j - 1, size),
                forall(t, range(0, k), arr[t] <= arr[k])
            )
        );
    }
}

void bubble_sort_sub(int arr[], int size) {
    requires(size > 0);
    ensures(forall(k, range(0, size), arr[k] <= arr[size - 1]));
    // doesn't work with `i < size - 1`
    for (int i = 0; i != size - 1; i += 1) {
        if (arr[i] > arr[i + 1]) {
            int tmp = arr[i + 1];
            arr[i + 1] = arr[i];
            arr[i] = tmp;
        }
        assert(forall(k, range(0, i + 1), arr[k] <= arr[i + 1]));
    }
}

void insertion_sort(int arr[], int size) {
    requires(size > 0);
    freeze(ARR, arr);
    // specification is still incomplete (e.g. ARR=[0,0,1], arr=[0,1, 1])
    ensures(
        forall(k, range(0, size - 1), arr[k] <= arr[k + 1])
        && forall(k, range(0, size), exists(t, range(0, size), ARR[k] == arr[t]))
    );
    for (int i = 1; i < size; i += 1) {
        int curr = arr[i];
        int j = 0;
        remember(i > 0 && j >= 0 && i < size);
        while (arr[j] < arr[i] && j < i) {
            assert(
                curr == arr[i]
                && j < i
                && arr[i] > arr[j]
                && forall(t, range(0, i - 1), arr[t] <= arr[t + 1])
                && forall(k, range(0, size), exists(t, range(0, size), ARR[k] == arr[t]))
            );
            j += 1;
        }
        remember(forall(t, range(0, i), arr[t] <= arr[t + 1]));
        for (int k = i; k > j; k -= 1) {
            arr[k] = arr[k - 1];
            assert(
                curr <= arr[j]
                && then(j > 0, curr > arr[j - 1])
                && forall(r, range(0, size), then(ARR[r] != curr, exists(t, range(0, size), t != k - 1 && ARR[r] == arr[t])))
                && k <= i
                && k > j
            );
        }
        arr[j] = curr;
        assert(
            forall(k, range(0, size), exists(t, range(0, size), ARR[k] == arr[t]))
        );
    }
}