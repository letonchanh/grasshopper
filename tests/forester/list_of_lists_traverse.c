#include <stdlib.h>
#include <verifier-builtins.h>

typedef struct l_node {
  int data;
  struct l_node* next;
} l_node_t;

typedef struct ll_node {
  struct l_node* lldata;
  struct ll_node* llnext;
} ll_node_t;

ll_node_t* ll_create() {
  ll_node_t* x = NULL;
  ll_node_t* y = NULL;

  while (__VERIFIER_nondet_int()) {
    y = malloc(sizeof(ll_node_t));
    y->llnext = x;
    l_node_t* u = NULL;
    l_node_t* v = NULL;
    while (__VERIFIER_nondet_int()) {
      v = malloc(sizeof(l_node_t));
      v->next = u;
      u = v;
    }
    y->lldata = u;
    x = y;
  }
  return x;
}

void list_destroy(l_node_t* lst) {
  l_node_t* x = lst;
  while (lst != NULL) {
    x = lst;
    lst = lst->next;
    free(x);
  }
}

void ll_destroy(ll_node_t* lst) {
  ll_node_t* x = lst;
  while (lst != NULL) {
    x = lst;
    lst = lst->llnext;
    list_destroy(x->lldata);
    free(x);
  }
}

ll_node_t* traverse(ll_node_t* x)
{
  ll_node_t* oc = x;
  while (oc != NULL)
  {
    l_node_t* ocdata = oc->lldata;
    ll_node_t* ocnext = oc->llnext;
    l_node_t* ic = ocdata;
    while (ic != NULL)
    {
      ic = ic->next;
    }
    oc = ocnext;
  }
  return x;
}

int main() {
  ll_destroy(traverse(ll_create()));
  return 0;
}

