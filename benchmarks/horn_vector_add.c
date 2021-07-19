#include "common.h"

void vector_add(int v[], int u[], int res[], int size) {
    requires(size > 0);
    ensures(forall(k, range(0, size), res[k] == v[k] + u[k]));
    for (int i = 0; i < size; i++) {
        res[i] = v[i] + u[i];
    }
}
