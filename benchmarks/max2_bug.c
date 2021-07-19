#include "common.h"

int max2_bug(int x, int y) {
    ensures(((ret == x) || (ret == y)) && (ret >= x) && (ret >= y));
    if (x > y * 2) { return x; }
    if (x > y) { return x; }
    return y;
}
