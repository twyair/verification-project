#ifndef ANNOTATIONS
#define requires(x)
#define ensures(x)
#define assert(x)
#define freeze(x, y)
#endif

bool de_morgan(bool x, bool y) {
    ensures(ret == (x && y));
    return ! (!x || !y);
}

bool de_morgan_bug(bool x, bool y) {
    ensures(ret == (x && y));
    return ! (!x || y);
}

int first_true(bool arr[], int size) {
    requires(size > 0);
    ensures(
        forall(k, range(0, size), then(arr[k] && forall(t, range(0, k), !arr[t]), ret == k))
        && then(forall(k, range(0, size), !arr[k]), ret == size)
    );
    for (int i = 0; i < size; i += 1) {
        if (arr[i]) {
            return i;
        }
        assert(i >= 0 && forall(k, range(0, i + 1), !arr[k]));
    }
    return size;
}

int flip_even(bool arr[], int size) {
    requires(size > 0);
    freeze(ARR, arr);
    ensures(
        forall(k, range(0, size), then(k % 2 == 0, arr[k] == !ARR[k]) && then(k % 2 == 1, arr[k] == ARR[k]))
    );
    for (int i = 0; i < size; i += 1) {
        if (i % 2 == 0) {
            arr[i] = !arr[i];
        }
        assert(
            i >= 0
            && forall(k, range(0, i + 1), then(k % 2 == 0, arr[k] == !ARR[k]))
            && forall(k, range(i+1, size), arr[k] == ARR[k])
            && forall(k, range(0, size), then(k % 2 == 1, arr[k] == ARR[k]))
        );
    }
}