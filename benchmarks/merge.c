#include "common.h"

void merge(int arr1[], int arr2[], int res[], int size1, int size2) {
    requires(
        size1 > 0 && size2 > 0
        && forall(t, range(0, size1 - 1), arr1[t] <= arr1[t+1])
        && forall(t, range(0, size2 - 1), arr2[t] <= arr2[t+1])
    );
    remember(
        size1 > 0 && size2 > 0
        && forall(t, range(0, size1 - 1), arr1[t] <= arr1[t+1])
        && forall(t, range(0, size2 - 1), arr2[t] <= arr2[t+1])
    );

    phantom(int perm1[]);
    phantom(int perm2[]);

    ensures(
        forall(t, range(size1 + size2 - 1), res[t] <= res[t+1])
        && forall(t1, range(0, size1), forall(t2, range(0, size2), perm1[t1] != perm2[t2]))
        && forall(t, range(0, size1), perm1[t] >= 0 && perm1[t] < size1 + size2 && res[perm1[t]] == arr1[t])
        && forall(t, range(0, size2), perm2[t] >= 0 && perm2[t] < size1 + size2 && res[perm2[t]] == arr2[t])
        && forall(t, range(0, size1 - 1), perm1[t + 1] > perm1[t])
        && forall(t, range(0, size2 - 1), perm2[t + 1] > perm2[t])
    );

    int i = 0;
    int j = 0;
    while (i < size1 || j < size2) {
        assert(
            i >= 0 && j >= 0 && i <= size1 && j <= size2
            && (i < size1 || j < size2)
            && then(i < size1 && i + j > 0, res[i + j - 1] <= arr1[i])
            && then(j < size2 && i + j > 0, res[i + j - 1] <= arr2[j])
            && forall(t, range(0, i + j - 1), res[t] <= res[t + 1])
            && forall(t, range(0, i), perm1[t] >= 0 && perm1[t] < i + j && res[perm1[t]] == arr1[t])
            && forall(t, range(0, j), perm2[t] >= 0 && perm2[t] < i + j && res[perm2[t]] == arr2[t])
            && forall(t, range(0, i - 1), perm1[t + 1] > perm1[t])
            && forall(t, range(0, j - 1), perm2[t + 1] > perm2[t])
            && forall(t1, range(0, i), forall(t2, range(0, j), perm1[t1] != perm2[t2]))
        );
        if (j >= size2 || i < size1 && arr1[i] < arr2[j]) {
            res[i + j] = arr1[i];
            phantom(perm1[i] = i + j);
            i++;
        } else {
            res[i + j] = arr2[j];
            phantom(perm2[j] = i + j);
            j++;
        }
    }
}
