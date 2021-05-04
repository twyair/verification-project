#include "common.h"

/* returns the square root of a perfect square
 * the result for non-perfect squares is undefined
 */
int sqrt_v2(int num) {
    requires(num > 0);
    ensures(then(exists(k, range(1, num), k * k == num), ret * ret == num));

    int bit = 1;
    while (bit * 4 <= num){
        assert(forall(k, range(1, bit), k * 4 <= num));
        bit *= 4;
    }

    int res = 0;
    while (bit != 0) {
        if (num >= res + bit) {
            num -= res + bit;
            res = res * 2 + bit;
        } else {
            res /= 2;
        }
        bit /= 4;
    }

    return res;
}

// TODO:
void merge(int arr1[], int arr2[], int res[], int size1, int size2) {
    requires(
        size1 > 0 && size2 > 0
        && forall(k, range(0, size1 - 1), arr1[k] <= arr1[k+1])
        && forall(k, range(0, size2 - 1), arr2[k] <= arr2[k+1])
    );
    ensures(forall(k, range(size1 + size2 - 1), res[k] <= res[k+1]));
}

/*
M(n) = n - 10, if n > 100
     = M(M(n + 11)), otherwise
*/
int mccarthy_91(int n) {
    ensures(then(n <= 100, ret == 91, ret == n - 10));
    freeze(N, n);
    int c = 1;
    while (c != 0) {
        if (n > 100) {
            n -= 10;
            c -= 1;
        } else {
            n += 11;
            c += 1;
        }
    }
    return n;
}

/*
 * taken from [https://github.com/dafny-lang/dafny/blob/master/Test/dafny4/BinarySearch.dfy]
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
