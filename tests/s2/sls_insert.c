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

node_t* sls_insert(node_t* lst, node_t* elt)
 //@ infer[G] requires lst::ll<> * elt::node<_, null> ensures G(res);
{
  if (lst == NULL || lst->data > elt->data) {
    elt->next = lst;
    return elt;
  } else {
    node_t* curr;
    curr = lst;
    while (curr->next != NULL && curr->next->data <= elt->data) 
    //@ infer[@shape] requires true ensures true;
    {
      curr = curr->next;
    }
    elt->next = curr->next;
    curr->next = elt;
    return lst;
  }
}
