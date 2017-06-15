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

node_t* sls_double_all(node_t* lst)
{
  if (lst == NULL) {
    return NULL;
  } else {
    node_t* curr, *cp;
    curr = lst;
    node_t* res = malloc(sizeof(node_t));
    cp = res;
    cp->data = 2 * curr->data;
    cp->next = NULL;
    while(curr->next != NULL) 
    {
      node_t* old_cp;
      old_cp = cp;
      cp = malloc(sizeof(node_t));
      old_cp->next = cp;
      curr = curr->next;
      cp->data = 2 * curr->data;
      cp->next = NULL;
    }
    return res;
  }
}

int main() {
  node_t* lst = list_create();
  node_t* copy_lst = sls_double_all(lst);
  list_destroy(lst);
  list_destroy(copy_lst);
  return 0;
}

