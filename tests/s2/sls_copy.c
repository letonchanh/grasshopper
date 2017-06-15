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
HeapPred G(node a, node b).
*/


node_t* copy(node_t* lst)
 //@ infer[G] requires lst::ll<> ensures G(lst, res);
{
  node_t* res;
  if (lst == NULL) {
    return NULL;
  } else {
    res = node_alloc();
    node_t* curr = lst;
    node_t* cp = res;
    cp->data = curr->data;
    cp->next = NULL;
    while (curr->next != NULL) 
    //@ infer[@shape] requires true ensures true;
    {
      node_t* old_cp;
      old_cp = cp;
      cp = node_alloc();
      old_cp->next = cp;
      curr = curr->next;
      cp->data = curr->data;
      cp->next = NULL;
    }
    return res;
  }
}
