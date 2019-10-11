//
// Created by yuxuan chen on 3/13/19.
//
#include <stdio.h>
extern int add();
extern int sub();
void print(int i) {
    printf("%d\n", i);
}
int s = add();
int main(int argc, char** argv){
    s = add();
    int i = 0;
    int j = 0;
    int x = 0;
    scanf("%d", &x);
    if (x > 3) i = add();
    else j = sub();
    print(i);
    print(j);
    print(s);
    return 0;
};

