#include "common.h"

bool de_morgan_bug(bool x, bool y) {
    ensures(ret == (x && y));
    return ! (!x || y);
}
