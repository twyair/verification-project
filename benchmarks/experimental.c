#include "common.h"

/* returns the square root of a perfect square
 * the result for non-perfect squares is undefined
 * [https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)]
 */
int sqrt_v3(int num) {
    requires(num > 1);
    freeze(NUM, num);
    ensures(ret * ret <= NUM && (ret + 1) * (ret + 1) > NUM);

    int bit = 1;
    while (bit * 4 <= num){
        assert(
            NUM > 1
            && num == NUM
            && forall(k, range(1, bit + 1), k * 4 <= num)
        );
        bit *= 4;
    }

    int res = 0;
    while (bit != 0) {
        assert(res >= 0 && num >= 0 && NUM > 1 && bit > 0 && num == NUM - res * res / bit / 4);
        if (num >= res + bit) {
            num -= res + bit;
            res = res / 2 + bit;
        } else {
            res /= 2;
        }
        bit /= 4;
    }

    return res;
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
    ensures(forall(t, range(size1 + size2 - 1), res[t] <= res[t+1]));
    int i = 0;
    int j = 0;
    while (i < size1 || j < size2) {
        assert(
            i >= 0 && j >= 0 && i <= size1 && j <= size2
            && (i < size1 || j < size2)
            && forall(t, range(0, i), exists(s, range(0, i + j), arr1[t] == res[s]))
            && forall(t, range(0, j), exists(s, range(0, i + j), arr2[t] == res[s]))
            && forall(t, range(0, i + j - 1), res[t] <= res[t + 1])
        );
        if (j >= size2 || arr1[i] < arr2[j]) {
            res[i + j] = arr1[i];
            i += 1;
        } else {
            res[i + j] = arr2[j];
            j += 1;
        }
    }
}

/*
 * taken from [https://github.com/dafny-lang/dafny/blob/master/Test/dafny4/BinarySearch.dfy]
 * FIXME: verification hangs
 */
int binary_search(int arr[], int size, int key) {
    requires(
        size > 0
        && forall(k, range(0, size - 1), arr[k] <= arr[k + 1])
    );
    remember(
        size > 0
        && forall(k, range(0, size - 1), arr[k] <= arr[k + 1])
    );
    ensures(then(
        exists(k, range(0, size), arr[k] == key),
        arr[ret] == key && ret < size && ret >= 0
    ));
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

// taken from [https://github.com/dafny-lang/dafny/blob/master/Test/dafny2/Classics.dfy]
// FIXME:
void additive_factorial(int n, int results[]) {
    requires(n >= 0);
    ensures(results[0] == 1 && forall(k, range(1, n), results[k] == k * results[k - 1]));
    results[0] = 1;
    int u = 1;
    int r = 1;
    while (r < n) {
        remember(1 <= r && r <= n && forall(k, range(1, r), results[k] == k * results[k - 1]));
        assert(0 == 0);
        int v = u;
        int s = 1;
        while (s <= r - 1) {
            u = u + v;
            s = s + 1;
            assert(1 <= s && s <= r && u == s * results[r - 1]);
        }
        results[r] = u;
        r = r + 1;
    }
}
