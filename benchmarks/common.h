#ifndef ANNOTATIONS
#include <stdbool.h>
#define requires(x)
#define ensures(x)
#define assert(x)
#define freeze(x, y)
#define remember(x)
#define phantom(x)
#define assume(x)
#else
#define is_nan(x) (!(x < 0.0 || x > 0.0 || x == 0.0 || x == -0.0))
#define phantom(x) x
#endif
