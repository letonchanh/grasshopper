struct node {
  int data; 
  struct node* next; 
};

/*@
ll<> == emp & self = null
    or self::node<_, q> * q::ll<> & self != null;
*/

struct node* node_alloc()
//@ requires true ensures res::node<_,_>;
;

/*@
HeapPred G(node a).
*/

struct node* sls_traverse(struct node* lst)
 //@ infer[G] requires lst::ll<> ensures G(res);
{
  struct node* curr;
  curr = lst;
  while (curr != NULL) 
  //@ infer[@shape] requires true ensures true;
  {
    curr = curr->next; 
  }
  return lst;
}

