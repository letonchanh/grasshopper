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

node_t* concat(node_t* a, node_t* b)
{
  if (a == NULL) {
    return b;
  } else {
    node_t* curr;
    curr = a;
    while(curr->next != NULL) 
    {
      curr = curr->next; 
    }
    curr->next = b;
    return a;
  }
}

int main() {
  list_destroy(concat(list_create(), list_create()));
  return 0;
}

