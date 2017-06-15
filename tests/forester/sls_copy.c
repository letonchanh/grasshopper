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

node_t* copy(node_t* lst)
{
  node_t* res;
  if (lst == NULL) {
    return NULL;
  } else {
    res = malloc(sizeof(node_t));
    node_t* curr = lst;
    node_t* cp = res;
    cp->data = curr->data;
    cp->next = NULL;
    while (curr->next != NULL) 
    {
      node_t* old_cp;
      old_cp = cp;
      cp = malloc(sizeof(node_t));
      old_cp->next = cp;
      curr = curr->next;
      cp->data = curr->data;
      cp->next = NULL;
    }
    return res;
  }
}

int main() {
  node_t* lst = list_create();
  node_t* copy_lst = copy(lst);
  list_destroy(lst);
  list_destroy(copy_lst);
  return 0;
}

