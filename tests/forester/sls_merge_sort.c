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
  
  node_t* last = res;

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

node_t* split(node_t* start)
{
  node_t* beforeMiddle = start;
  node_t* middle = start->next;
  node_t* last = middle;
  
  while (last != NULL && last->next != NULL)
  {
    beforeMiddle = middle;
    middle = middle->next;
    last = last->next;
    if (last != NULL) {
      last = last->next;
    }
  }
  beforeMiddle->next = NULL;
  
  return middle;
}


node_t* merge_sort(node_t* x)
{
  if (x == NULL || x->next == NULL) return x;
	
  node_t* x2 = split(x);
  node_t* res1 = merge_sort(x);
  node_t* res2 = merge_sort(x2);
  node_t* res = merge(res1, res2);
  return res;
} 

int main() {
  list_destroy(merge_sort(list_create()));
  return 0;
}

