#!/bin/bash

# Print usage:
[ $# -eq 0 ] && { echo -e "Usage: $0 <folder>\nWill add struct definitions and functions and convert *.spl files in <folder> to *.c."; exit 1; }

for file in $1/*.spl; do
    cat - <<EOF	> ${file%%.*}.c
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

EOF
    cat $file | \
	sed -e 's/null/NULL/g;' \
	    -e 's/:=/=/g' \
	    -e 's/\([a-zA-Z]\)\.\([a-zA-Z]\)/\1->\2/g' \
	    -e 's/ returns.*$//' \
	    -e '/^include/d' \
	    -e 's/^\([ ]*\)procedure/\1node_t*/' \
	    -e 's/\([a-zA-Z_][a-zA-Z_]*\)[ ]*: Node/node_t* \1/g' \
	    -e 's/\([a-zA-Z_][a-zA-Z_]*\)[ ]*: Int/int \1/g' \
	    -e 's/^\([ ]*\)var \([a-zA-Z_][a-zA-Z_]*\) = /\1node_t* \2 = /' \
	    -e 's/^\([ ]*\)var /\1/' \
	    -e 's/new Node/node_alloc()/' \
	    -e 's/free \([a-zA-Z_][a-zA-Z_]*\);/free(\1);/' \
	    -e 's/^\([ ]\)*requires.*$/\1\/\/@ infer\[G\] requires lst::ll<> ensures G(res);/' \
	    -e '/^[ ]*ensures/d' \
	    -e '/^[ ]*invariant/d' \
	    -e 's/^\([ ]*\)\(while.*\)$/\1\2\n\1\/\/@ infer\[@shape\] requires true ensures true;/' \
	>> ${file%%.*}.c
done
