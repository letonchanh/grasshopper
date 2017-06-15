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

/*@
HeapPred G(node a).
*/

void sls_dispose(node_t* lst)
 //@ infer[G] requires lst::ll<> ensures G(lst);
{
  node_t* curr = lst;
  while (curr != NULL) 
  //@ infer[@shape] requires true ensures true;
  {
    node_t* tmp = curr;
    curr = curr->next; 
    free(tmp);
  }
}
