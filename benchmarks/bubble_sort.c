#ifndef ANNOTATIONS
#define requires(x)
#define ensures(x)
#define assert(x)
#endif

int bubble_sort(int arr[], int size) {
    requires(size > 0);
    ensures(forall(k, range(0, size - 1), arr[k] <= arr[k + 1]));
    for (int j = 0; j < size; j += 1) {
        for (int i = 0; i < size - j - 1; i += 1) {
            if (arr[i] > arr[i + 1]) {
                int tmp = arr[i + 1];
                arr[i + 1] = arr[i];
                arr[i] = tmp;
            }
            assert(forall(k, range(0, i + 1), arr[k] <= arr[i + 1]));
        }
        assert(forall(k, range(size - j - 1, size),
                      forall(t, range(0, k), arr[t] <= arr[k])));
    }
}