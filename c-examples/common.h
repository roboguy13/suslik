#ifndef COMMON_H
#define COMMON_H

#include <stdio.h>
#include <stdlib.h>

typedef struct List {
  int payload;
  struct List* next;
} List;

void cons(int newPayload, List** xs) {
  List* head = malloc(sizeof(List));

  head->payload = newPayload;
  head->next = *xs;

  *xs = head;
}

void snoc(int newPayload, List** xs) {
  if (*xs == NULL) {
    cons(newPayload, xs);
  } else {
    snoc(newPayload, &((*xs)->next));
  }
}

int last(List* xs) {
  if (xs == NULL) {
    printf("last: empty list\n");
    exit(1);
  }

  if (xs->next == NULL) {
    return xs->payload;
  } else {
    return last(xs->next);
  }
}

int sum(List* xs) {
  if (xs == NULL) {
    return 0;
  } else {
    return xs->payload + sum(xs->next);
  }
}

void print_int_list(List* xs) {
  printf("[");

  List* curr = xs;

  while (curr != 0) {
    printf("%d", curr->payload);

    if (curr->next != 0) {
      printf(", ");
    }

    curr = curr->next;
  }

  printf("]");
}

List* to_int_list(int* arr, int size) {
  if (size == 0) {
    return NULL;
  }

  List* n = malloc(sizeof(List));

  n->payload = arr[0];
  n->next = to_int_list(arr+1, size-1);
  return n;
}

List* build_int_list(int start, int end) {
  List* n = malloc(sizeof(List));
  List* original = n;

  for (int i = start; i < end; ++i) {
    n->payload = i;

    if (i != end-1) {
      n->next = malloc(sizeof(List));
      n = n->next;
    }
  }

  n->next = 0;

  return original;
}

// In the acual implementation, we use defunctionalization instead of function
// pointers
typedef int (*IntBinOp)(int, int);

void zipWith(IntBinOp f, List* xs, List* ys, List** result) {
  if (xs == NULL || ys == NULL) {
    *result = NULL;
    return;
  }

  List* node = malloc(sizeof(List));

  node->payload = f(xs->payload, ys->payload);
  node->next = NULL;

  zipWith(f, xs->next, ys->next, &node->next);

  *result = node;
}

void scanl1_go(IntBinOp f, List* xs, List** result, int currVal) {
  if (xs == NULL) {
  } else {
    int nextVal = f(currVal, xs->payload);
    scanl1_go(f, xs->next, result, nextVal);
    cons(nextVal, result);
  }
}

void scanl1(IntBinOp f, List* xs, List** result) {
  if (xs == NULL) {
    printf("Error: scanl1: empty list\n");
    exit(1);
  }

  scanl1_go(f, xs->next, result, xs->payload);
  cons(xs->payload, result);
}

////

void scanr1_go(IntBinOp f, List* xs, List** result, int currVal) {
  if (xs->next == NULL) {
    cons(xs->payload, result);
  } else {
    scanr1_go(f, xs->next, result, currVal);

    int nextVal = f(xs->payload, (*result)->payload);
    cons(nextVal, result);
  }
}

void scanr1(IntBinOp f, List* xs, List** result) {
  if (xs == NULL) {
    printf("Error: scanr1: empty list\n");
    exit(1);
  }

  scanr1_go(f, xs, result, last(xs));
}

////

int min(int x, int y) { return x <= y ? x : y; }
int max(int x, int y) { return x <= y ? y : x; }

int add(int x, int y) { return x + y; }
int sub(int x, int y) { return x - y; }

#endif

