#include <stdlib.h>
#include <verifier-builtins.h>

#define LIST(lst) \
  node_t* lst = NULL; \
  lst_y = NULL; \
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

node_t* lst_y;

int main() {
  LIST(a);
  LIST(b);
  
  if (a == NULL) {
    a = b;
  } else {
    node_t* curr;
    curr = a;
    while(curr->next != NULL) 
    {
      curr = curr->next; 
    }
    curr->next = b;
  }

  DESTROY(a);
  return 0;
}

