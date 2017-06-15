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

node_t* filter (node_t* x)
 
{
  node_t* curr = x;
  node_t* prv = NULL;
  while (curr != NULL) 
  {
    node_t* old_curr = curr;
    curr = curr->next;
    if (__VERIFIER_nondet_int()) {
      if (prv != NULL) {
        prv->next = curr;
      } else {
        x = curr;
      }
      free(old_curr);
    } else {
      prv = old_curr;
    }
  }
  return x;
}

int main() {
  list_destroy(filter(list_create()));
  return 0;
}

