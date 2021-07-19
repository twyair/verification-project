#include "common.h"

float max2_float(float x, float y) {
    // `requires` is used to avoid cases where x or y are nan
    requires(x < y || x > y);
    ensures(((ret == x) || (ret == y)) && (ret >= x) && (ret >= y));
    if (x > y) {
        return x;
    }
    return y;
}
