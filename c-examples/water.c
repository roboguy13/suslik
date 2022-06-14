// See https://chrisdone.com/posts/twitter-problem-loeb/

#include <stdio.h>
#include <stdlib.h>

#include "common.h"

/*
   water :: [Int] -> Int
   water h =
    sum (zipWith (-)
                 (zipWith min
                          (scanl1 max h)
                          (scanr1 max h))
                 h)
  */

int water(List* h) {
  List* left_max = NULL;
  List* right_max = NULL;

  List* zipWith_min_list = NULL;
  List* zipWith_sub_list = NULL;

  scanl1(max, h, &left_max);
  scanr1(max, h, &right_max);

  zipWith(min, left_max, right_max, &zipWith_min_list);
  zipWith(sub, zipWith_min_list, h, &zipWith_sub_list);

  return sum(zipWith_sub_list);
}

int main() {
  int arr[] = {2,5,1,2,3,4,7,7,6};
  List* h = to_int_list(arr, 9);

  print_int_list(h);

  printf("\nResult: %d\n", water(h));

  return 0;
}

