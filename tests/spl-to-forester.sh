#!/bin/bash

# Print usage:
[ $# -eq 0 ] && { echo -e "Usage: $0 <folder>\nWill add struct definitions and functions and convert *.spl files in <folder> to *.c."; exit 1; }

for file in $1/*.spl; do
    cat - <<EOF	> ${file%%.*}.c
#include <stdlib.h>
#include <verifier-builtins.h>

typedef struct node {
  int data;
  struct node* next;
} node_t;

node_t* list_create() {
  node_t* x = NULL;
  node_t* y = NULL;

  while (__VERIFIER_nondet_int()) {
    y = malloc(sizeof(node_t));
    y->next = x;
    x = y;
  }
  return x;
}

node_t* singleton() {
  node_t* x = malloc(sizeof(node_t));
  x-> next = NULL;
  return x;
}


void list_destroy(node_t* lst) {
  node_t* x = lst;
  while (lst != NULL) {
    x = lst;
    lst = lst->next;
    free(x);
  }
}
EOF
    cat $file | \
	sed -e 's/null/NULL/g;' \
	    -e 's/:=/=/g' \
	    -e 's/\([a-zA-Z]\)\.\([a-zA-Z]\)/\1->\2/g' \
	    -e '/^include/d' \
	    -e '/^[ ]*requires/d' \
	    -e '/^[ ]*ensures/d' \
	    -e '/^[ ]*invariant/d' \
	    -e 's/ returns.*$//' \
	    -e 's/^\([ ]*\)procedure/\1node_t*/' \
	    -e 's/\([a-zA-Z_][a-zA-Z_]*\)[ ]*: Node/node_t* \1/g' \
	    -e 's/\([a-zA-Z_][a-zA-Z_]*\)[ ]*: Int/int \1/g' \
	    -e 's/^\([ ]*\)var \([a-zA-Z_][a-zA-Z_]*\) = /\1node_t* \2 = /' \
	    -e 's/^\([ ]*\)var /\1/' \
	    -e 's/new Node/malloc(sizeof(node_t))/' \
	    -e 's/free \([a-zA-Z_][a-zA-Z_]*\);/free(\1);/' \
	>> ${file%%.*}.c
    cat - <<EOF >> ${file%%.*}.c

int main() {
  list_destroy(traverse(list_create()));
  return 0;
}

EOF
done
