#include "common.h"

int array_max(int arr[], int size) {
    requires(size > 0);
    ensures(
        forall(k, range(0, size), arr[k] == 0)
    );
    for (int i = 0; i != size; i++) {
        arr[i] = 0;
    }
}
