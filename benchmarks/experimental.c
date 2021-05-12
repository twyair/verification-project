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
            && pow4[pow4_index] == bit
            && then(bit > 1, bit / 4 * 4 == bit)
            && forall(i, range(1, pow4_index + 1), pow4[i] == 4 * pow4[i - 1])
            && pow4[0] == 1
            && pow4_index >= 0
            && NUM * 4 * bit - num * 4 * bit == res * res
            && num < 2 * res + bit * 4
        );
        // FIXME: prove that `res % 2 == 0`
        assume(res % 2 == 0);
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
