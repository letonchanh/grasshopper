
typedef struct t_node {
  int data;
  struct t_node* left;
  struct t_node* right;
} t_node_t;

typedef struct lt_node {
  struct t_node* ltdata;
  struct lt_node* ltnext;
} lt_node_t;

/*@
tree<> == emp & self = null
    or self::t_node<_, l, r> * l::tree<> * r::tree<> & self != null;

lt<> == emp & self = null
    or self::lt_node<t, n> * t::tree<> * n::lt<> & self != null;
*/

/*@
HeapPred G1(t_node a).
HeapPred G2(lt_node a).
*/


void traverse_tree(t_node_t* t)
 //@ infer[G1] requires t::tree<> & t != null ensures G1(t);
{
  if (t->left != NULL)
  {
    traverse_tree(t->left);
  }
  if (t->right != NULL)
  {
    traverse_tree(t->right);
  }
}

void traverse(lt_node_t* l)
 //@ infer[G2] requires l::lt<> ensures G2(l);
{
  lt_node_t* oc = l;
  while (oc != NULL)
  //@ infer[@shape] requires true ensures true;
  {
    if (l->ltdata != NULL)
    {
      traverse_tree(l->ltdata);
    }
    oc = oc->ltnext;
  }
}
