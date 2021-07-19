void assert(int condition);
void ensures(int postcondition);
extern int ret;

#define N 100
#define SWAP(X,Y) { tmp = (X); (X) = (Y); (Y) = tmp; }

/**
 * Same, but indices are also given as an array.
 */
int max3_array_indirect(int arr[N], int is[3]) {
    /**/ ensures(((ret == arr[is[0]]) || (ret == arr[is[1]]) || (ret == arr[is[2]]))
                  && (ret >= arr[is[0]]) && (ret >= arr[is[1]]) && (ret >= arr[is[2]])); /**/

    if (arr[is[0]] > arr[is[1]]) {
        if (arr[is[0]] > arr[is[2]]) return arr[is[0]];
    }
    else {
        if (arr[is[1]] > arr[is[2]]) return arr[is[1]];
    }
    return arr[is[2]];
}
