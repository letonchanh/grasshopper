
typedef struct l_node {
  int data;
  struct l_node* next;
} l_node_t;

typedef struct tl_node {
  struct l_node* tldata;
  struct tl_node* tlleft;
  struct tl_node* tlright;
} tl_node_t;

/*@
list<> == emp & self = null
    or self::l_node<_, q> * q::list<> & self != null;

tl<> == emp & self = null
    or self::tl_node<d, l, r> * d::list<> * l::tl<> * r::tl<> & self != null;
*/

/*@
HeapPred G1(l_node a).
HeapPred G2(tl_node a).
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

void traverse(tl_node_t* t)
 //@ infer[G2] requires t::tl<> ensures G2(t);
{
  if (t->tldata != NULL)
  {
    traverse_list(t->tldata);
  }
  if (t->tlleft != NULL)
  {
    traverse(t->tlleft);
  }
  if (t->tlright != NULL)
  {
    traverse(t->tlright);
  }
}
