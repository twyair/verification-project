#ifndef ANNOTATIONS
#define requires(x)
#define ensures(x)
#define assert(x)
#define freeze(x, y)
#else
#define is_nan(x) (!(x < 0.0 || x > 0.0 || x == 0.0 || x == -0.0))
#endif
