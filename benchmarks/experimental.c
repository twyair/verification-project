#include "common.h"

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

    assert(NUM > 1 && num == NUM && bit * 4 > num && bit <= num && pow4[pow4_index] == bit && forall(i, range(1, pow4_index + 1), pow4[i] == 4 * pow4[i - 1]) && pow4[0] == 1 && pow4_index >= 0);

    int res = 0;
    while (bit != 0) {
        assert(
            res >= 0
            && num >= 0
            && NUM > 1
            && bit > 0
            && num * 4 * bit == NUM * 4 * bit - res * res
            && pow4[pow4_index] == bit
            && forall(i, range(1, pow4_index + 1), pow4[i] == 4 * pow4[i - 1])
            && pow4[0] == 1
            && pow4_index >= 0
        );
        if (num >= res + bit) {
            num -= res + bit;
            res = res / 2 + bit;
        } else {
            res /= 2;
        }
        bit /= 4;
        phantom(pow4_index -= 1);
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
            i += 1;
        } else {
            res[i + j] = arr2[j];
            phantom(perm2[j] = i + j);
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
