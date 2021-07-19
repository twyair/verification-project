void ensures(int postcondition);
extern int ret;

/**
 * (still same)
 */
int max3_v3(int x, int y, int z) {
    /**/ ensures(((ret == x) || (ret == y) || (ret == z))
                 && (ret >= x) && (ret >= y) && (ret >= z)); /**/
    int tmp = x;
    if (y > tmp) tmp = y;
    if (z > tmp) tmp = z;
    return tmp;
}
