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


node_t* filter (node_t* x)
 //@ infer[G] requires x::ll<> ensures G(res);
{
  node_t* curr = x;
  node_t* prv = NULL;
  while (curr != NULL) 
  //@ infer[@shape] requires true ensures true;
  {
    node_t* old_curr = curr;
    curr = curr->next;
    if (nondet()) {
      if (prv != NULL) {
        prv->next = curr;
      } else {
        x = curr;
      }
      free(old_curr);
    } else {
      prv = old_curr;
    }
  }
  return x;
}
