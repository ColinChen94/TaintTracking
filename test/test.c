#include <stdio.h>
int main() {
    int w, x, y, z;
    int i = 0, j = 0;
    scanf("%d %d %d %d", &w, &x, &y, &z);
    if (w > 0) {
        if (x > 0) {
	    i = 1;
	}
    }

    if (y > 0) {
        j = z;
    }
    if (j > 0) {
        j = 1;
    }
    printf("%d %d\n", i, j);
    return 0;
}

