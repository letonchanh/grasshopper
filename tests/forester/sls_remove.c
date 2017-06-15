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

node_t* remove(node_t* lst, int value)
{
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
  return lst;
}

int main() {
  list_destroy(remove(list_create(), __VERIFIER_nondet_int()));
  return 0;
}

