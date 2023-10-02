#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void printInt(int n) { printf("%d\n", n); }

extern void printString(const char* str) {
    if (str == NULL)
        printf("\n");
    else
        printf("%s\n", str);
}

int readInt() {
    int n;
    scanf("%d", &n);
    return n;
}

char* readString() {
    char* str = NULL;
    size_t len = 0;

    if (getline(&str, &len, stdin) == -1) {
        printf("readString getline error\n");
        exit(1);
    }
    len = strlen(str);
    if (str[len - 1] == '\n') 
        str[len - 1] = '\0';

    return str;
}

void error() {
    printf("runtime error\n");
    exit(1);
}

char* ____concatStr(char* s1, char* s2) {
    if (s1 == NULL) return s2;
    if (s2 == NULL) return s1;

    size_t len1 = strlen(s1);
    size_t len2 = strlen(s2);
    char* result = malloc(len1 + len2 + 1);

    memcpy(result, s1, len1);
    memcpy(result + len1, s2, len2);
    result[len1 + len2] = '\0';

    return result;
}

int ____compareStr(char* s1, char* s2) {
    int res;
    if (s1 == NULL && s2 != NULL) {
        res = strcmp("", s2);
    } else if (s1 != NULL && s2 == NULL) {
        res = strcmp(s1, "");
    } else if (s1 == NULL && s2 == NULL) {
        return 0;
    } else {
        res = strcmp(s1, s2);
    }

    return res;
}

void* ____calloc(size_t a, size_t b) {
    return calloc(a, b);
}