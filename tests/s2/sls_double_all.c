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
HeapPred G(node a, node b).
*/

node_t* sls_double_all(node_t* lst)
 //@ infer[G] requires lst::ll<> ensures G(lst, res);
{
  if (lst == NULL) {
    return NULL;
  } else {
    node_t* curr, *cp;
    curr = lst;
    node_t* res = node_alloc();
    cp = res;
    cp->data = 2 * curr->data;
    cp->next = NULL;
    while(curr->next != NULL) 
    //@ infer[@shape] requires true ensures true;
    {
      node_t* old_cp;
      old_cp = cp;
      cp = node_alloc();
      old_cp->next = cp;
      curr = curr->next;
      cp->data = 2 * curr->data;
      cp->next = NULL;
    }
    return res;
  }
}
