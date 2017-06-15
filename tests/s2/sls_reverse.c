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


node_t* reverse(node_t* lst)
 //@ infer[G] requires lst::ll<> ensures G(res);
{
  node_t* curr;
  curr = lst;
  node_t* rev = NULL;
  while (curr != NULL)
  //@ infer[@shape] requires true ensures true;
  {
    node_t* tmp;
    tmp = curr;
    curr = curr->next;
    tmp->next = rev;
    rev = tmp;
  }
  
  return rev;
}
