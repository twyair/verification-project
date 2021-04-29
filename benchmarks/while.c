int foo(int arr[100]) {
    ensures(ret >= arr[0]);
    int tmp = arr[0];
    int i = 0;
    while(i < 100) {
        assert(tmp >= arr[0]);
        if (arr[i] > tmp) tmp = arr[i];
        i = i + 1;
    }
    return tmp;
}

int foo2(int arr[100]) {
    ensures(ret >= arr[0]);
    int tmp = arr[0];
    int i = 0;
    do {
        assert(tmp >= arr[0]);
        if (arr[i] > tmp) tmp = arr[i];
        i = i + 1;
    } while (i < 100);
    return tmp;
}

int foo3(int arr[100]) {
    ensures(ret >= arr[0]);
    int tmp = arr[0];
    for(int i = 0; i < 100; i += 1) {
        assert(tmp >= arr[0]);
        if (arr[i] > tmp) tmp = arr[i];
        i = i + 1;
    }
    return tmp;
}