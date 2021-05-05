#include "common.h"

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
        forall(k, range(0, size),
            then(
                k % 2 == 0,
                arr[k] == !ARR[k],
                arr[k] == ARR[k]
            )
        )
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

int array_max(int arr[], int size) {
    requires(size > 0);
    ensures(
        exists(k, range(0, size), ret == arr[k])
        && forall(k, range(0, size), arr[k] <= ret)
    );
    int max = arr[0];
    for (int i = 0; i != size; i += 1) {
        if (arr[i] >= max) {
            max = arr[i];
        }
        assert(exists(k, range(0, i + 1), max == arr[k]) && forall(k, range(0, i + 1), arr[k] <= max));
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

void array_reverse(int arr[], int size) {
    requires(size > 0);
    freeze(ARR, arr);
    ensures(forall(k, range(0, size), ARR[k] == arr[size - 1 - k]));
    for (int i = 0; i < size / 2; i += 1) {
        int tmp = arr[i];
        arr[i] = arr[size - 1 - i];
        arr[size - 1 - i] = tmp;
        assert(
            size > 0
            && i >= 0
            && forall(k, range(0, i + 1), arr[k] == ARR[size - 1 - k] && arr[size - 1 - k] == ARR[k])
            && forall(k, range(i + 1, (size + 1) / 2), arr[k] == ARR[k] && arr[size - 1 - k] == ARR[size - 1 - k])
        );
    }
}

void vector_add(int v[], int u[], int res[], int size) {
    requires(size > 0);
    for(int i = 0; i < size; i += 1) {
        res[i] = v[i] + u[i];
        assert(forall(k, range(0, i + 1), res[k] == v[k] + u[k]));
    }
    assert(forall(k, range(0, size), res[k] == v[k] + u[k]));
}

bool is_prime(int num) {
    requires(num > 1);
    remember(num > 1);
    ensures(forall(k, range(2, num), num % k != 0) == ret);
    for (int i = 2; i != num; i += 1) {
        if (num % i == 0) {
            return 0 != 0;
        }
        assert(i >= 2 && i < num && forall(k, range(2, i + 1), num % k != 0));
    }
    return 0 == 0;
}

int sqrt_v1(int num) {
    requires(num > 0);
    // FIXME? doesnt work with `, ret == -1)`
    ensures(then(exists(k, range(1, num), k * k == num), ret * ret == num));
    for (int i = 1; i < num; i += 1) {
        if (i * i == num) {
            return i;
        }
        assert(i >= 1 && forall(k, range(0, i+1), k * k != num));
    }
    return -1;
}

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
    for (int _j = 0; first < size && arr[first] < sep; first += 1) {
        assert(
            first < size
            && forall(k, range(0, first + 1), arr[k] < sep)
            && forall(t, range(0, size), exists(k, range(0, size), arr[k] == ARR[t]))
        );
    }
    if (first == size) {
        return size;
    }

    for (int i = first + 1; i < size; i += 1) {
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
            first += 1;
        }

    }
    return first;
}

int mccarthy_91(int n) {
    freeze(N, n);
    ensures(then(N <= 101, ret == 91, ret == N - 10));
    int c = 1;
    while (c != 0) {
        if (n > 100) {
            n -= 10;
            c -= 1;
        } else {
            n += 11;
            c += 1;
        }
        assert(
            then(
                N > 100,
                c == 0 && n == N - 10,
                c >= 0
                && n <= 10 * c + 91
                && (n >= 91 || c > 0)
            )
        );
    }
    return n;
}