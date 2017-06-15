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
HeapPred G(node a).
*/


node_t* remove(node_t* lst, int value)
 //@ infer[G] requires lst::ll<> ensures G(res);
{
  node_t* curr, * prv;
  prv = NULL;
  curr = lst;
  while (curr != NULL && curr->data < value)
  //@ infer[@shape] requires true ensures true;
  {
    prv = curr;
    curr = curr->next;
  }
  if (curr != NULL && curr->data == value) {
    if (prv == NULL) {
      lst = curr->next;
    } else {
      prv->next = curr->next;
    }
    free(curr);
  }
  return lst;
}
