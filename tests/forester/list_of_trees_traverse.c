#include <stdlib.h>
#include <verifier-builtins.h>

typedef struct t_node {
  int data;
  struct t_node* left;
  struct t_node* right;
} t_node_t;

typedef struct lt_node {
  struct t_node* ltdata;
  struct lt_node* ltnext;
} lt_node_t;

t_node_t* t_create() {
  if (__VERIFIER_nondet_int())
    return NULL;
  else {
    t_node_t* x = malloc(sizeof(t_node_t));
    x->left = t_create();
    x->right = t_create();
    return x;
  }
}

lt_node_t* lt_create() {
  lt_node_t* x = NULL;
  lt_node_t* y = NULL;

  while (__VERIFIER_nondet_int()) {
    y = malloc(sizeof(lt_node_t));
    y->ltnext = x;
    y->ltdata = t_create();
    x = y;
  }
  return x;
}

void t_destroy(t_node_t* x) {
  if (x != NULL) {
    t_destroy(x->left);
    t_destroy(x->right);
    free(x);
  }
}

void lt_destroy(lt_node_t* lst) {
  lt_node_t* x = lst;
  while (lst != NULL) {
    x = lst;
    lst = lst->ltnext;
    t_destroy(x->ltdata);
    free(x);
  }
}

void traverse_tree(t_node_t* t)
{
  if (t->left != NULL)
  {
    traverse_tree(t->left);
  }
  if (t->right != NULL)
  {
    traverse_tree(t->right);
  }
}

lt_node_t* traverse(lt_node_t* l)
{
  lt_node_t* oc = l;
  while (oc != NULL)
  {
    if (l->ltdata != NULL)
    {
      traverse_tree(l->ltdata);
    }
    oc = oc->ltnext;
  }
  return l;
}

int main() {
  lt_destroy(traverse(lt_create()));
  return 0;
}

