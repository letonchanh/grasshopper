typedef struct node {
  int data; 
  struct node* next; 
} node_t;

/*@
ll<> == emp & self = null
    or self::node<_, q> * q::ll<> & self != null;
*/

node_t* node_alloc()
//@ requires true ensures res::node<_,_>;
;

void free(node_t* x)
//@ requires x::node<_,_> ensures emp;
;

int nondet()
//@ requires emp ensures emp;
;

/*@
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a).
*/


node_t* merge(node_t* a, node_t* b)
 //@ infer[G1] requires a::ll<> * b::ll<> ensures G1(res);
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
  //@ infer[@shape] requires true ensures true;
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

node_t* pull_strands(node_t* lst, node_t** res2)
 //@ infer[G2] requires lst::ll<> ensures G2(res, res2);
{
  node_t* sorted_tail, *curr, *prv;
  node_t* rest = lst->next;
  curr = rest;
  prv = NULL;
  node_t* sorted = lst;
  sorted_tail = sorted;
  sorted_tail->next = NULL;
  while (curr != NULL)
  //@ infer[@shape] requires true ensures true;
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
  *res2 = rest;
  return sorted;
}

node_t* strand_sort(node_t* lst)
 //@ infer[G3] requires lst::ll<> ensures G3(res);
{
  node_t* sorted;
  sorted = NULL;
  while (lst != NULL)
  //@ infer[@shape] requires true ensures true;
  {
    node_t* new_sorted;
    new_sorted = pull_strands(lst, &lst);
    sorted = merge(sorted, new_sorted);
  }
  return sorted;
}
