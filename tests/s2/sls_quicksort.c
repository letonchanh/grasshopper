typedef struct node {
  int data; 
  struct node* next; 
} node_t;

/*@
ll<> == emp & self = null
    or self::node<_, q> * q::ll<> & self != null;
lseg<y> == emp & self = y
    or self::node<_, q> * q::lseg<y> & self != y;
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
HeapPred G1(node a, node b, node c).
HeapPred G2(node a, node b).
*/


node_t* split(node_t* x, node_t* y)
 //@ infer[G1] requires x::lseg<y> ensures G1(x, y, res);
{
  node_t* curr = x->next;
  node_t* pivot;
  pivot = x;

  while (curr != y) 
  //@ infer[@shape] requires true ensures true;
  {
    if (curr->data < pivot->data) {
      int tmp = curr->data;
      curr->data = pivot->next->data;
      pivot->next->data = pivot->data;
      pivot->data = tmp;
      pivot = pivot->next;
    }
    curr = curr->next;
  }
  return pivot;
}

void quicksort(node_t* x, node_t* y)
 //@ infer[G2] requires x::lseg<y> ensures G2(x, y);
{
  if (x != y && x->next != y) {
    node_t* pivot = split(x, y);
    quicksort(x, pivot);
    quicksort(pivot->next, y);
  }
}
