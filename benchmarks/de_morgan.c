#include "common.h"

bool de_morgan(bool x, bool y) {
    ensures(ret == (x && y));
    return ! (!x || !y);
}
