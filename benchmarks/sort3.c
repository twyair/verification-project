void assert(int condition);
void ensures(int postcondition);
extern int ret;

#define N 100
#define SWAP(X,Y) { tmp = (X); (X) = (Y); (Y) = tmp; }

void sort3(int arr[N], int i) {
    int tmp;

    if (arr[i] > arr[i + 1]) SWAP(arr[i], arr[i + 1]);
    if (arr[i + 1] > arr[i + 2]) SWAP(arr[i + 1], arr[i + 2]);
    if (arr[i] > arr[i + 1]) SWAP(arr[i], arr[i + 1]);

    /**/ assert((arr[i] <= arr[i + 1]) && (arr[i + 1] <= arr[i + 2])); /**/
}
