#ifndef ANNOTATIONS
#define requires(x)
#define ensures(x)
#define assert(x)
#endif

int array_max(int arr[], int size) {
    requires(size > 0);
    ensures(forall(k, range(0, size), arr[k] <= ret));
    int max = arr[0];
    for (int i = 0; i < size; i += 1) {
        if (arr[i] > max) {
            max = arr[i];
        }
        assert(forall(k, range(0, i + 1), arr[k] <= max));
    }
    return max;
}