#ifndef ANNOTATIONS
#define requires(x)
#define ensures(x)
#define assert(x)
#endif

int array_max(int arr[], int size) {
    requires(size > 0);
    ensures(
        exists(k, range(0, size), ret == arr[k])
        && forall(k, range(0, size), arr[k] <= ret)
    );
    int max = arr[0];
    for (int i = 0; i < size; i += 1) {
        if (arr[i] >= max) {
            max = arr[i];
        }
        assert(forall(k, range(0, i + 1), arr[k] <= max));
    }
    return max;
}

int max2(int x, int y) {
    ensures(((ret == x) || (ret == y)) && (ret >= x) && (ret >= y));
    if (x > y) {
        return x;
    }
    return y;
}

int max2_wrong(int x, int y) {
    ensures(((ret == x) || (ret == y)) && (ret >= x) && (ret >= y));
    if (x > y * 2) { return x; }
    if (x > y) { return x; }
    return y;
}

float max2_float(float x, float y) {
    // `requires` is used to avoid cases where x or y are nan
    requires(x < y || x > y);
    ensures(((ret == x) || (ret == y)) && (ret >= x) && (ret >= y));
    if (x > y) {
        return x;
    }
    return y;
}