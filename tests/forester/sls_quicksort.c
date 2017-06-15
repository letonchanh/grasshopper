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

node_t* split(node_t* x, node_t* y)
{
  node_t* curr = x->next;
  node_t* pivot;
  pivot = x;

  while (curr != y) 
  {
    if (curr->data < pivot->data) {
      int tmp = curr->data;
      curr->data = pivot->next->data;
      pivot->next->data = pivot->data;
      pivot->data = tmp;
      pivot = pivot->next;
    }
    curr = curr->next;
  }
  return pivot;
}

void quicksort(node_t* x, node_t* y)
{
  if (x != y && x->next != y) {
    node_t* pivot = split(x, y);
    quicksort(x, pivot);
    quicksort(pivot->next, y);
  }
}

int main() {
  node_t* lst = list_create();
  quicksort(lst, NULL);
  list_destroy(lst);
  return 0;
}

