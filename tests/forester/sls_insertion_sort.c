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

void insertion_sort(node_t* lst) 
{
  node_t* prv;
  prv = NULL;
  node_t* srt;
  srt = lst;
  while (srt != NULL)
  {
    node_t* curr;
    curr = srt->next;
    node_t* min;
    min = srt;
    while (curr != NULL)    
    {
      if (curr->data < min->data) {
        min = curr;
      }
      curr = curr->next;
    }
    int tmp = min->data;
    min->data = srt->data;
    srt->data = tmp;
    prv = srt;
    srt = srt->next;
  }
}

int main() {
  node_t* lst = list_create();
  insertion_sort(lst);
  list_destroy(lst);
  return 0;
}

