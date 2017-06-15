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

void insertion_sort(node_t* lst) 
 //@ infer[G] requires lst::ll<> ensures G(lst);
{
  node_t* prv;
  prv = NULL;
  node_t* srt;
  srt = lst;
  while (srt != NULL)
  //@ infer[@shape] requires true ensures true;
  {
    node_t* curr;
    curr = srt->next;
    node_t* min;
    min = srt;
    while (curr != NULL)    
    //@ infer[@shape] requires true ensures true;
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
