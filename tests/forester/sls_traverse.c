#include <stdlib.h>
#include <verifier-builtins.h>

typedef struct node {
  int data;
  struct node* next;
} node_t;

node_t* list_create() {
  node_t* x = NULL;
  node_t* y = NULL;

  while (__VERIFIER_nondet_int()) {
    y = malloc(sizeof(node_t));
    y->next = x;
    x = y;
  }
  return x;
}

void list_destroy(node_t* lst) {
  node_t* x = lst;
  while (lst != NULL) {
    x = lst;
    lst = lst->next;
    free(x);
  }
}

node_t* sls_traverse(node_t* lst)
{
  node_t* curr;
  curr = lst;
  while (curr != NULL) 
  {
    curr = curr->next; 
  }
  return lst;
}


int main() {
  list_destroy(sls_traverse(list_create()));
  return 0;
}

