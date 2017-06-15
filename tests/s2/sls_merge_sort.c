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
  
  node_t* last = res;

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

node_t* split(node_t* start)
 //@ infer[G2] requires start::ll<> ensures G2(start, res);
{
  node_t* beforeMiddle = start;
  node_t* middle = start->next;
  node_t* last = middle;
  
  while (last != NULL && last->next != NULL)
  //@ infer[@shape] requires true ensures true;
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
 //@ infer[G3] requires x::ll<> ensures G3(res);
{
  if (x == NULL || x->next == NULL) return x;
	
  node_t* x2 = split(x);
  node_t* res1 = merge_sort(x);
  node_t* res2 = merge_sort(x2);
  node_t* res = merge(res1, res2);
  return res;
} 
