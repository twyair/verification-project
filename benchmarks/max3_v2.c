void ensures(int postcondition);
extern int ret;

/**
 * (same)
 */
int max3_v2(int x, int y, int z) {
    /**/ ensures(((ret == x) || (ret == y) || (ret == z))
                 && (ret >= x) && (ret >= y) && (ret >= z)); /**/
    if (x > y) {
        if (x > z) return x;
    }
    else {
        if (y > z) return y;
    }
    return z;
}