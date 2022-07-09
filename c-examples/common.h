#ifndef COMMON_H
#define COMMON_H

#include <stdio.h>
#include <stdlib.h>
#include <functional>

template<typename T>
struct List {
  T payload;
  List<T>* next;
};

template<typename T>
void cons(T newPayload, List<T>** xs) {
  List<T>* head = new List<T>;

  head->payload = newPayload;
  head->next = *xs;

  *xs = head;
}

template<typename T>
void snoc(T newPayload, List<T>** xs) {
  if (*xs == NULL) {
    cons(newPayload, xs);
  } else {
    snoc(newPayload, &((*xs)->next));
  }
}

template<typename T>
T last(List<T>* xs) {
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

template<typename T>
T sum(List<T>* xs) {
  if (xs == NULL) {
    return 0;
  } else {
    return xs->payload + sum(xs->next);
  }
}

void print_int_list(List<int>* xs) {
  printf("[");

  List<int>* curr = xs;

  while (curr != 0) {
    printf("%d", curr->payload);

    if (curr->next != 0) {
      printf(", ");
    }

    curr = curr->next;
  }

  printf("]");
}

List<int>* to_int_list(int* arr, int size) {
  if (size == 0) {
    return NULL;
  }

  List<int>* n = new List<int>;

  n->payload = arr[0];
  n->next = to_int_list(arr+1, size-1);
  return n;
}

List<int>* build_int_list(int start, int end) {
  List<int>* n = new List<int>;
  List<int>* original = n;

  for (int i = start; i < end; ++i) {
    n->payload = i;

    if (i != end-1) {
      n->next = new List<int>;
      n = n->next;
    }
  }

  n->next = 0;

  return original;
}

void print_list_of_lists(List<List<int>* >* xss) {
  List<List<int>* >* curr = xss;

  while (curr != 0) {
    print_int_list(curr->payload);
    printf("\n");

    curr = curr->next;
  }
}

List<List<int>*> * build_list_of_lists(int width, int height) {
  List<List<int>*>* n = new List<List<int>*>;
  List<List<int>*>* original = n;

  for (int i = 0; i < width*height; i += width) {
    n->payload = build_int_list(i, i+width);

    if (i != width * (height-1)) {
      n->next = new List<List<int>*>;
      n = n->next;
    }
  }

  n->next = 0;

  return original;
}
// In the acual implementation, we use defunctionalization instead of function
// pointers
template<typename T>
using BinOp = T (*)(T, T);
// typedef int (*IntBinOp)(int, int);

//  { sll(xs, sX) ** sll(ys, sY) ** result :-> 0 } ~>
//  { zipWith(f, xs, ys, sX, sY, sResult) ** result :-> r ** sll(r, sResult) }
template<typename T>
void zipWith(BinOp<T> f, List<T>* xs, List<T>* ys, List<T>** result) {
  // OPEN
  if (xs == NULL) {
    //  { xs == 0 && sX =i {} ; sll(ys, sY) ** result :-> 0 } ~>
    //  { zipWith(xs, ys, sX, sY, sResult) ** result :-> r ** sll(r, sResult) }

    // WRITE
    //   { ... } ~>
    //   { ... ** result :-> 0 }
    *result = NULL;
  } else {
    //  { xs != 0 && sX =i {xV} ++ sX1 ; sll(ys, sY) ** result :-> 0 } ~>
    //  { zipWith(xs, ys, sX, sY, sResult) ** result :-> r ** sll(r, sResult) }

    if (ys == NULL) {
      // WRITE
      //   { ... } ~>
      //   { ... ** result :-> 0 }
      *result = NULL;
    } else {
      //  { xs != 0 && sX =i {xV} ++ sY1 && ys != 0 && sY =i {yV} ++ sY1 ; sll(ys, sY) ** result :-> 0 } ~>
      //  { zipWith(xs, ys, sX, sY, sResult) ** result :-> r ** sll(r, sResult) }

      // ALLOC
      //  { ... } ~>
      //  { ... ** [node, 2] }
      List<T>* node = new List<T>;

      // WRITE
      //   
      node->payload = f(xs->payload, ys->payload);
      node->next = NULL;

      zipWith(f, xs->next, ys->next, &node->next);

      *result = node;
    }
  }
}

template<typename T>
void scanl1_go(BinOp<T> f, List<T>* xs, List<T>** result, T currVal) {
  if (xs == NULL) {
  } else {
    int nextVal = f(currVal, xs->payload);
    scanl1_go(f, xs->next, result, nextVal);
    cons(nextVal, result);
  }
}

template<typename T>
void scanl1(BinOp<T> f, List<T>* xs, List<T>** result) {
  if (xs == NULL) {
    printf("Error: scanl1: empty list\n");
    exit(1);
  }

  scanl1_go(f, xs->next, result, xs->payload);
  cons(xs->payload, result);
}

////

template<typename T>
void scanr1_go(BinOp<T> f, List<T>* xs, List<T>** result, T currVal) {
  if (xs->next == NULL) {
    cons(xs->payload, result);
  } else {
    scanr1_go(f, xs->next, result, currVal);

    int nextVal = f(xs->payload, (*result)->payload);
    cons(nextVal, result);
  }
}

template<typename T>
void scanr1(BinOp<T> f, List<T>* xs, List<T>** result) {
  if (xs == NULL) {
    printf("Error: scanr1: empty list\n");
    exit(1);
  }

  scanr1_go(f, xs, result, last(xs));
}

////

template<typename T>
void append(List<T>* xs, List<T>* ys, List<T>** result) {
  if (xs == NULL) {
    if (ys == NULL) {
      *result = NULL;
    } else {
      List<T>* n = new List<T>;
      n->payload = ys->payload;

      *result = n;

      append<T>(NULL, ys->next, &(n->next));
    }
  } else {
    List<T>* n = new List<T>;

    n->payload = xs->payload;

    *result = n;

    append(xs->next, ys, &n->next);
  }
}

template<typename T>
void copy(List<T>* xs, List<T>** result) {
  append<T>(NULL, xs, result);
}

////

template<typename A, typename B>
void map(std::function<void(A, B*)> fn, List<A>* xs, List<B>** result) {
  if (xs == NULL) {
    *result = NULL;
  } else {
    B* acc = new B;

    fn(xs->payload, acc);

    List<B>* n = new List<B>;
    n->payload = *acc;

    List<B>* m = NULL;
    map(fn, xs->next, &m);

    n->next = m;
    *result = n;
  }
}

////

int min(int x, int y) { return x <= y ? x : y; }
int max(int x, int y) { return x <= y ? y : x; }

int add(int x, int y) { return x + y; }
int sub(int x, int y) { return x - y; }

#endif

