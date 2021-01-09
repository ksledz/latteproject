#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>

void printInt(int x) {
	printf("%d\n", x);
}

void printString(char *s) {
	printf("%s\n", s);
}

void error() {
	exit(1);
}

int readInt() {
	int i;
	scanf("%d", &i);
	return i;
}

char *readString() {
	char *res = 0;
	size_t n = 0;
	getline(&res, &n, stdin);
	return res;
}

char *$concat(char *a, char *b) {
	char *res = malloc(strlen(a) + strlen(b) + 1);
	strcpy(res, a);
	strcat(res, b);
	return res;
}
