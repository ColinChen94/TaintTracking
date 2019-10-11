//
// Created by yuxuan chen on 3/13/19.
//
#include <stdio.h>
extern int add();
extern int sub();
void print(int i) {
    printf("%d\n", i);
}
struct Double {
    int i[2];
    int j;
};
int main(int argc, char** argv){
    struct Double temp;
    temp.i[0] = 0;
    temp.j = 0;
    int x = 0;
    scanf("%d", &x);
    if (x > 3) temp.i[x] = add();
    else temp.j = sub();
    print(temp.i[x]);
    print(temp.j);
    return 0;
};

