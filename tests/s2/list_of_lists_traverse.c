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
HeapPred G(ll_node a).
*/

void traverse(ll_node_t* x)
 //@ infer[G] requires x::ll<> ensures G(x);
{
  ll_node_t* oc = x;
  while (oc != NULL)
  //@ infer[@shape] requires true ensures true;
  {
    l_node_t* ocdata = oc->lldata;
    ll_node_t* ocnext = oc->llnext;
    l_node_t* ic = ocdata;
    while (ic != NULL)
    //@ infer[@shape] requires true ensures true;
    {
      ic = ic->next;
    }
    oc = ocnext;
  }
}
