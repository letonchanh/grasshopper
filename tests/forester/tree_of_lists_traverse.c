#include <stdlib.h>
#include <verifier-builtins.h>

typedef struct node {
  int data;
  struct node* next;
} node_t;

typedef struct tl_node {
  struct node* tldata;
  struct tl_node* tlleft;
  struct tl_node* tlright;
} tl_node_t;

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

tl_node_t* tl_create() {
  if (__VERIFIER_nondet_int())
    return NULL;
  else {
    tl_node_t* x = malloc(sizeof(tl_node_t));
    x->tlleft = tl_create();
    x->tlright = tl_create();
    x->tldata = list_create();
    return x;
  }
}

void list_destroy(node_t* lst) {
  node_t* x = lst;
  while (lst != NULL) {
    x = lst;
    lst = lst->next;
    free(x);
  }
}

void tl_destroy(tl_node_t* x) {
  if (x != NULL) {
    tl_destroy(x->tlleft);
    tl_destroy(x->tlright);
    list_destroy(x->tldata);
    free(x);
  }
}

void traverse_list(node_t* l)
{
  node_t* c = l;
  while (c != NULL)
  {
    c = c->next;
  }
}

void traverse(tl_node_t* t)
{
  if (t->tldata != NULL)
  {
    traverse_list(t->tldata);
  }
  if (t->tlleft != NULL)
  {
    traverse(t->tlleft);
  }
  if (t->tlright != NULL)
  {
    traverse(t->tlright);
  }
}

int main() {
  tl_node_t* tl = tl_create();
  if (tl != NULL) traverse(tl);
  tl_destroy(tl);
  return 0;
}

