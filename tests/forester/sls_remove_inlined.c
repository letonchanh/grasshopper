#include <stdlib.h>
#include <verifier-builtins.h>

#define LIST(lst) \
  node_t* lst = NULL; \
  node_t* lst_y = NULL; \
  while (__VERIFIER_nondet_int()) { \
    lst_y = malloc(sizeof(node_t)); \
    lst_y->next = lst; \
    lst = lst_y; \
  }

#define SINGLETON(elt) \
  node_t* elt = malloc(sizeof(node_t)); \
  elt->next = NULL;

#define DESTROY(lst) \
  node_t* x_lst = lst; \
  while (lst != NULL) { \
    x_lst = lst; \
    lst = lst->next; \
    free(x_lst); \
  }

typedef struct node {
  int data;
  struct node* next;
} node_t;

int main() {
  LIST(lst);
  int value = __VERIFIER_nondet_int();

  node_t* curr, *prv;
  prv = NULL;
  curr = lst;
  while (curr != NULL && curr->data < value)
  {
    prv = curr;
    curr = curr->next;
  }
  if (curr != NULL && curr->data == value) {
    if (prv == NULL) {
      lst = curr->next;
    } else {
      prv->next = curr->next;
    }
    free(curr);
  }

  DESTROY(lst);
  return 0;
}

