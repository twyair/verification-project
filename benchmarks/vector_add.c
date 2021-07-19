#include "common.h"

void vector_add(int v[], int u[], int res[], int size) {
    requires(size > 0);
    for (int i = 0; i < size; i++) {
        res[i] = v[i] + u[i];
        assert(forall(k, range(0, i + 1), res[k] == v[k] + u[k]));
    }
    assert(forall(k, range(0, size), res[k] == v[k] + u[k]));
}
