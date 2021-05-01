#ifndef ANNOTATIONS
#define requires(x)
#define ensures(x)
#define assert(x)
#endif

// doesn't work
void bubble_sort(int arr[], int size) {
    requires(size > 0);
    ensures(forall(k, range(0, size - 1), arr[k] <= arr[k + 1]));
    for (int j = 0; j < size; j += 1) {
        for (int i = 0; i != size - j - 1; i += 1) {
            if (arr[i] > arr[i + 1]) {
                int tmp = arr[i + 1];
                arr[i + 1] = arr[i];
                arr[i] = tmp;
            }
            assert(
                forall(k, range(0, i + 1), arr[k] <= arr[i + 1])
                /*&& forall(k, range(size - j - 1, size - 1), arr[k] <= arr[k + 1])*/
                && forall(
                    k, range(size - j, size),
                    forall(t, range(0, k), arr[t] <= arr[k])
                )
            );
        }
        assert(
            forall(
                /*k, range(size - j - 2, size - 1),
                then(k >= 0, arr[k] <= arr[k + 1])*/
                k, range(size - j - 1, size),
                forall(t, range(0, k), arr[t] <= arr[k])
            )
        );
    }
}

void bubble_sort_sub(int arr[], int size) {
    requires(size > 0);
    ensures(forall(k, range(0, size), arr[k] <= arr[size - 1]));
    // doesn't work with `i < size - 1`
    for (int i = 0; i != size - 1; i += 1) {
        if (arr[i] > arr[i + 1]) {
            int tmp = arr[i + 1];
            arr[i + 1] = arr[i];
            arr[i] = tmp;
        }
        assert(forall(k, range(0, i + 1), arr[k] <= arr[i + 1]));
    }
}