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

/*@
HeapPred G(node a).
*/

node_t* concat(node_t* a, node_t* b)
 //@ infer[G] requires a::ll<> * b::ll<> ensures G(res);
{
  if (a == NULL) {
    return b;
  } else {
    node_t* curr;
    curr = a;
    while(curr->next != NULL) 
    //@ infer[@shape] requires true ensures true;
    {
      curr = curr->next; 
    }
    curr->next = b;
    return a;
  }
}
