typedef struct l_node {
  int data;
  struct l_node* next;
} l_node_t;

typedef struct ll_node {
  struct l_node* lldata;
  struct ll_node* llnext;
} ll_node_t;

/*@
list<> == emp & self = null
    or self::l_node<_, q> * q::list<> & self != null;

ll<> == emp & self = null
    or self::ll_node<l, n> * l::list<> * n::ll<> & self != null;
*/

/*@
HeapPred G1(l_node a).
HeapPred G2(ll_node a).
*/

void traverse_list(l_node_t* l)
 //@ infer[G1] requires l::list<> ensures G1(l);
{
  l_node_t* c = l;
  while (c != NULL)
  //@ infer[@shape] requires true ensures true;
  {
    c = c->next;
  }
}

void traverse(ll_node_t* x)
 //@ infer[G2] requires x::ll<> ensures G2(x);
{
  ll_node_t* oc = x;
  while (oc != NULL)
  //@ infer[@shape] requires true ensures true;
  {
    traverse_list(oc->lldata);
    oc = oc->llnext;
  }
}
