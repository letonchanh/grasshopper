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

node_t* singleton() {
  node_t* x = malloc(sizeof(node_t));
  x-> next = NULL;
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

node_t* sls_insert(node_t* lst, node_t* elt)
{
  if (lst == NULL || lst->data > elt->data) {
    elt->next = lst;
    return elt;
  } else {
    node_t* curr;
    curr = lst;
    while (curr->next != NULL && curr->next->data <= elt->data) 
    {
      curr = curr->next;
    }
    elt->next = curr->next;
    curr->next = elt;
    return lst;
  }
}

int main() {
  list_destroy(sls_insert(list_create(), singleton()));
  return 0;
}

