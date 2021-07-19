#include "common.h"

void insertion_sort(int arr[], int size) {
    requires(size > 0);
    freeze(ARR, arr);
    phantom(int perm[]);
    phantom(int perm_rev[]);
    assume(forall(k, range(0, size), perm[k] == k));
    assume(forall(k, range(0, size), perm_rev[k] == k));
    ensures(
        forall(k, range(0, size - 1), arr[k] <= arr[k + 1])
        && forall(k, range(0, size), perm[k] < size && perm[k] >= 0 && arr[k] == ARR[perm[k]])
        && forall(k, range(0, size), perm_rev[k] < size && perm_rev[k] >= 0 && arr[perm_rev[k]] == ARR[k])
        && forall(k, range(0, size), perm[perm_rev[k]] == k)
    );
    for (int i = 1; i < size; ++i) {
        int curr = arr[i];
        int j = 0;
        remember(
            i > 0 && j >= 0 && i < size
            && forall(t, range(0, size), perm[t] < size && perm[t] >= 0 && arr[t] == ARR[perm[t]])
        );
        while (arr[j] < arr[i] && j < i) {
            assert(
                curr == arr[i]
                && j < i
                && arr[i] > arr[j]
                && forall(t, range(0, i - 1), arr[t] <= arr[t + 1])
                && forall(k, range(0, size), perm_rev[k] < size && perm_rev[k] >= 0 && arr[perm_rev[k]] == ARR[k])
                && forall(k, range(0, size), perm[perm_rev[k]] == k)
            );
            j++;
        }

        phantom(int p = perm[i]);
        remember(forall(t, range(0, i), arr[t] <= arr[t + 1]));
        for (int k = i; k > j; k -= 1) {
            arr[k] = arr[k - 1];
            phantom(perm[k] = perm[k - 1]);
            phantom(perm_rev[perm[k]] = k);
            assert(
                curr <= arr[j]
                && then(j > 0, curr > arr[j - 1])
                && ARR[p] == curr && p < size && p >= 0
                && forall(t, range(0, size), then(t != p, perm_rev[t] < size && perm_rev[t] >= 0 && arr[perm_rev[t]] == ARR[t]))
                && forall(t, range(0, size), then(t != p, perm[perm_rev[t]] == t))
                && forall(t, range(0, size), then(t != p, perm_rev[t] != k - 1))
                && k <= i && k > j
            );
        }
        arr[j] = curr;
        phantom(perm[j] = p);
        phantom(perm_rev[p] = j);
        assert(
            forall(k, range(0, size), perm_rev[k] < size && perm_rev[k] >= 0 && arr[perm_rev[k]] == ARR[k])
            && forall(k, range(0, size), perm[perm_rev[k]] == k)
        );
    }
}
