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

node_t* merge(node_t* a, node_t* b)
{
  node_t* res = NULL;
  if (a == NULL) {
    return b;
  } else if (b == NULL) {
    return a;
  } else if (a->data <= b->data) {
    res = a;
    a = a->next;
  } else {
    res = b;
    b = b->next;
  }
  
  node_t* last;
  last = res;

  while (a != NULL || b != NULL)
  {
    if (a == NULL || b != NULL && a->data > b->data) {
      last->next = b;
      last = b;
      b = b->next;
    } else {
      last->next = a;
      last = a;
      a = a->next;
    }
  }

  return res;
}

node_t* pull_strands(node_t* lst, node_t** res)
{
  node_t* sorted_tail, *curr, *prv;
  node_t* rest = lst->next;
  curr = rest;
  prv = NULL;
  node_t* sorted = lst;
  sorted_tail = sorted;
  sorted_tail->next = NULL;
  while (curr != NULL)
  {
    if (curr->data >= sorted_tail->data) {
      node_t* old_curr;
      old_curr = curr;
      curr = curr->next; 
      sorted_tail->next = old_curr;
      sorted_tail = old_curr;
      old_curr->next = NULL;
      if (rest == old_curr) {
        rest = curr;
      }
      if (prv != NULL) {
        prv->next = curr;
      }
    } else {
      prv = curr;
      curr = curr->next;
    }
  }
  *res = rest;
  return sorted;
}

node_t* strand_sort(node_t* lst)
{
  node_t* sorted;
  sorted = NULL;
  while (lst != NULL)
  {
    node_t* new_sorted;
    new_sorted = pull_strands(lst, &lst);
    sorted = merge(sorted, new_sorted);
  }
  return sorted;
}

int main() {
  list_destroy(strand_sort(list_create()));
  return 0;
}

