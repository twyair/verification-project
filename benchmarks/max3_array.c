void assert(int condition);
void ensures(int postcondition);
extern int ret;

#define N 100
#define SWAP(X,Y) { tmp = (X); (X) = (Y); (Y) = tmp; }

/**
 * Computes the maximal of three array elements.
 */
int max3_array(int arr[N], int i, int j, int k) {
    /**/ ensures(((ret == arr[i]) || (ret == arr[j]) || (ret == arr[k]))
                 && (ret >= arr[i]) && (ret >= arr[j]) && (ret >= arr[k])); /**/

    if (arr[i] > arr[j]) {
        if (arr[i] > arr[k]) return arr[i];
    }
    else {
        if (arr[j] > arr[k]) return arr[j];
    }
    return arr[k];
}

