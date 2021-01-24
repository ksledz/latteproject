#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <stdbool.h>
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
	char *res;
	scanf("%ms", &res);
	return res;
}

char *$concat(char *a, char *b) {
	char *res = malloc(strlen(a) + strlen(b) + 1);
	strcpy(res, a);
	strcat(res, b);
	return res;
}

int *$newarrayint(int num) {
	char *alloc = calloc (1, 16 + num * sizeof (int));
	if (!alloc) error();
	int *res = (int *)(alloc + 16);
	res[-1] = num;
	return res;
}

bool *$newarraybool(int num) {
	char *alloc = calloc (1, 16 + num);
	if (!alloc) error();
	int *res = (int *)(alloc + 16);
	res[-1] = num;
	return (bool*)res;
}

char **$newarraystr(int num) {
	char *alloc = calloc (1, 16 + num * sizeof (void *));
	if (!alloc) error();
	int *lptr = (int *)(alloc + 16);
	lptr[-1] = num;
	char **res = (void*)lptr;
	for (int i = 0; i < num; i++)
		res[i] = "";
	return res;
}

void *$newarrayptr(int num) {
	char *alloc = calloc (1, 16 + num * sizeof (void *));
	if (!alloc) error();
	int *res = (int *)(alloc + 16);
	res[-1] = num;
	return res;
}

void *$newobject(int sz) {
	char *res = calloc(1, sz);
	if (!res) error();
	return res;
}
