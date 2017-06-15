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

node_t* sls_pairwise_sum(node_t* x, node_t* y)
{
  if (x == NULL || y == NULL) {
    return NULL;
  }
  node_t* z = malloc(sizeof(node_t));
  node_t* curr_x = x;
  node_t* curr_y = y;
  node_t* last_z = z;
  z->data = curr_x->data + curr_y->data;
  z->next = NULL;
  while (curr_x->next != NULL && curr_y->next != NULL) 
  {
    node_t* tmp = last_z;
    curr_x = curr_x->next;
    curr_y = curr_y->next;
    last_z = malloc(sizeof(node_t));
    last_z->next = NULL;
    last_z->data = curr_x->data + curr_y->data;        
    tmp->next = last_z;
  }
  return z;
}

int main() {
  node_t* a = list_create();
  node_t* b = list_create();
  list_destroy(sls_pairwise_sum(a, b));
  list_destroy(a);
  list_destroy(b);
  return 0;
}

