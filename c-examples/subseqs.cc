
/* subseqs :: [a] -> [[a]]
   subseqs = foldr (\x xss -> map (x:) xss ++ xss) [[]]
 */

#include <stdio.h>
#include <stdlib.h>

#include "common.h"

void map_cons(int x, List<List<int>* >* xs, List<List<int>* >** result) {
  if (xs == NULL) {
    *result = NULL;
  } else {
    List<int>* listCopy = NULL;
    copy(xs->payload, &listCopy);
    cons(x, &listCopy);

    List<List<int>*>* n = new List<List<int>*>;
    n->payload = listCopy;

    List<List<int>*>* m = NULL;
    map_cons(x, xs->next, &m);
    n->next = m;

    *result = n;
  }

  // map<List<int>*, List<int>* >(
  //   [x]
  //     (List<int>* a, List<int>** b) {
  //       List<int>* n = NULL;
  //       copy<int>(a, &n);
  //       cons(x, &n);
  //       copy(n, b);
  //     }
  //   ,xs
  //   ,result);
}

// map (x:) xss ++ xss
void map_cons_append(int x, List<List<int>* >* xs, List<List<int>* >** result) {
  List<List<int>*>* inter = NULL;
  map_cons(x, xs, &inter);
  append(inter, xs, result);
}

void foldr_op(int x, List<List<int>* >* acc, List<List<int>* >** result) {
  map_cons_append(x, acc, result);
}

void foldr_subseqs(List<int>* input, List<List<int>* >* acc, List<List<int>* >** output) {
  if (input == NULL) {
    copy(acc, output);
  } else {
    List<List<int>*>* inter = NULL;

    foldr_subseqs(input->next, acc, &inter);
    foldr_op(input->payload, inter, output);

    // foldr_op(input->payload, acc, &inter);
    //
    // foldr_subseqs(input->next, inter, output);
  }
}

/* subseqs :: [a] -> [[a]]
   subseqs = foldr (\x xss -> map (x:) xss ++ xss) [[]]
 */
void subseqs(List<int>* input, List<List<int>*>** result) {
  List<List<int>*>* singletonListOfLists = NULL;

  cons<List<int>*>(NULL, &singletonListOfLists);

  foldr_subseqs(input, singletonListOfLists, result);
}

int main() {
  List<int>* xs = build_int_list(0, 5);

  /*
  print_int_list(xs);

  List<int>* ys = NULL;
  copy(xs, &ys);
  printf("\nresult:\n");
  print_int_list(ys);
  */

  List<List<int>*>* r = NULL;

  subseqs(xs, &r);
  printf("result:\n");
  print_list_of_lists(r);

  // List<List<int>*>* xss = build_list_of_lists(5, 5);
  //
  // print_list_of_lists(xss);
  //
  // List<List<int>*>* r = NULL;
  //
  // printf("\nresult:\n");
  // map_cons_append(-2, xss, &r);
  // print_list_of_lists(r);


  // int arr[] = {2,5,1,2,3,4,7,7,6};
  // List<int>* xs = to_int_list(arr, 9);
  // List<int>* ys = to_int_list(arr, 9);
  //
  // List<int>* r = NULL;
  //
  // append(xs, ys, &r);
  // print_int_list(r);
  //
  return 0;
}

