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
HeapPred G(node a, node b, node c).
*/


node_t* sls_pairwise_sum(node_t* x, node_t* y)
 //@ infer[G] requires x::ll<> * y::ll<> ensures G(x, y, res);
{
  if (x == NULL || y == NULL) {
    return NULL;
  }
  node_t* z = node_alloc();
  node_t* curr_x = x;
  node_t* curr_y = y;
  node_t* last_z = z;
  z->data = curr_x->data + curr_y->data;
  z->next = NULL;
  while (curr_x->next != NULL && curr_y->next != NULL) 
  //@ infer[@shape] requires true ensures true;
  {
    node_t* tmp = last_z;
    curr_x = curr_x->next;
    curr_y = curr_y->next;
    last_z = node_alloc();
    last_z->next = NULL;
    last_z->data = curr_x->data + curr_y->data;        
    tmp->next = last_z;
  }
  return z;
}
