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
    for (int i = 0; i < size; i++) {
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
    for (int i = 0; i < size; i++) {
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
    for (int i = 0; i != size; i++) {
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

int max2_bug(int x, int y) {
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
    for (int i = 0; i < size / 2; i++) {
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
    for (int i = 0; i < size; i++) {
        res[i] = v[i] + u[i];
        assert(forall(k, range(0, i + 1), res[k] == v[k] + u[k]));
    }
    assert(forall(k, range(0, size), res[k] == v[k] + u[k]));
}

bool is_prime(int num) {
    requires(num > 1);
    remember(num > 1);
    ensures(forall(k, range(2, num), num % k != 0) == ret);
    for (int i = 2; i != num; i++) {
        if (num % i == 0) {
            return false;
        }
        assert(i >= 2 && i < num && forall(k, range(2, i + 1), num % k != 0));
    }
    return true;
}

// taken from [https://github.com/dafny-lang/dafny/blob/master/Test/dafny2/Classics.dfy]
int additive_factorial(int n) {
    requires(n >= 0);
    phantom(int results[]);
    ensures(results[n] == ret && forall(k, range(1, n + 1), results[k] == k * results[k - 1]) && results[0] == 1);
    phantom(results[0] = 1);
    int u = 1;
    int r = 1;
    while (r <= n) {
        remember(1 <= r && r <= n && forall(k, range(1, r), results[k] == k * results[k - 1]) && results[0] == 1);
        int v = u;
        assert(results[r - 1] == v && v == u);
        int s = 1;
        while (s <= r - 1) {
            u = u + v;
            s = s + 1;
            assert(1 <= s && s <= r && u == s * results[r - 1]  && results[r - 1] == v);
        }
        phantom(results[r] = u);
        r = r + 1;
    }
    return u;
}

int sqrt_v1(int num) {
    requires(num > 0);
    // FIXME? doesnt work with `, ret == -1)`
    ensures(then(exists(k, range(1, num), k * k == num), ret * ret == num));
    for (int i = 1; i < num; i++) {
        if (i * i == num) {
            return i;
        }
        assert(i >= 1 && forall(k, range(0, i+1), k * k != num));
    }
    return -1;
}

int sqrt_v2(int num) {
    requires(num > 0);
    ensures(ret * ret <= num && (ret + 1) * (ret + 1) > num);
    int i = 1;
    while (i * i <= num) {
        assert(i >= 1 && i <= num && forall(k, range(0, i + 1), k * k <= num));
        i++;
    }
    return i - 1;
}

/* returns the square root of a perfect square
 * the result for non-perfect squares is undefined
 * [https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)]
 */
int sqrt_v3(int num) {
    requires(num > 1);
    freeze(NUM, num);
    ensures(ret * ret <= NUM && (ret + 1) * (ret + 1) > NUM);

    phantom(int pow4[]);
    phantom(int pow4_index = 0);

    int bit = 1;
    phantom(pow4[0] = 1);
    while (bit * 4 <= num){
        assert(
            NUM > 1
            && num == NUM
            && pow4[pow4_index] == bit
            && forall(i, range(1, pow4_index + 1), pow4[i] == 4 * pow4[i - 1])
            && pow4[0] == 1
            && bit * 4 <= num
            && pow4_index >= 0
        );
        bit *= 4;
        phantom(pow4_index += 1);
        phantom(pow4[pow4_index] = bit);
    }

    phantom(int X = 0);
    int res = 0;
    while (bit != 0) {
        assert(
            res >= 0
            && num >= 0
            && NUM > 1
            && bit > 0
            && pow4[pow4_index] == bit
            && then(bit > 1, bit / 4 * 4 == bit)
            && forall(i, range(1, pow4_index + 1), pow4[i] == 4 * pow4[i - 1])
            && pow4[0] == 1
            && pow4_index >= 0
            && NUM * 4 * bit - num * 4 * bit == res * res
            && num < 2 * res + bit * 4
            && res == X * (bit * 4)
        );
        if (num >= res + bit) {
            num -= res + bit;
            res = res / 2 + bit;
            phantom(X = 2 * X + 1);
        } else {
            res /= 2;
            phantom(X *= 2);
        }
        bit /= 4;
        phantom(pow4_index -= 1);
    }

    return res;
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

int mccarthy_91(int n) {
    freeze(N, n);
    ensures(then(N <= 101, ret == 91, ret == N - 10));
    int c = 1;
    while (c != 0) {
        if (n > 100) {
            n -= 10;
            c--;
        } else {
            n += 11;
            c++;
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

int binary_search(int arr[], int size, int key) {
    requires(
        size > 0
        && forall(k, range(0, size - 1), arr[k] <= arr[k + 1])
    );
    ensures(then(
        exists(k, range(0, size), arr[k] == key),
        arr[ret] == key && ret < size && ret >= 0,
        ret == -1
    ));
    phantom({
        remember(
            forall(k, range(0, size - 1), arr[k] <= arr[k + 1])
        );
        for (int i = 0; i < size; i++) {
            for (int j = i; j >= 0; j--) {
                assert(
                    forall(k, range(0, i), forall(t, range(0, k + 1), arr[t] <= arr[k]))
                    && forall(t, range(j, i + 1), arr[t] <= arr[i])
                    && i < size && i >= 0
                    && j >= 0 && j <= i
                );
            }
            assert(
                forall(k, range(0, i + 1), forall(t, range(0, k + 1), arr[t] <= arr[k]))
                && i < size && i >= 0
            );
        }
    });
    remember(
        forall(k, range(0, size), forall(t, range(0, k + 1), arr[t] <= arr[k]))
    );
    int lo = 0;
    int hi = size;
    while (lo < hi) {
        assert(
            lo >= 0
            && hi > lo
            && hi <= size
            && forall(k, range(0, lo), arr[k] < key)
            && forall(k, range(hi, size), arr[k] > key)
        );
        int mid = (lo + hi) / 2;
        if (key < arr[mid]) {
            hi = mid;
        } else if (arr[mid] < key) {
            lo = mid + 1;
        } else {
            return mid;
        }
    }
    return -1;
}

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

void bubble_sort(int arr[], int size) {
    requires(size > 0);
    ensures(forall(k, range(0, size - 1), arr[k] <= arr[k + 1]));
    for (int j = 0; j < size; j++) {
        for (int i = 0; i != size - j - 1; i++) {
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