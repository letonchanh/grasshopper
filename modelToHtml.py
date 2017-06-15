import re
import argparse
import os

header = """\
<!doctype html>
<html>
<head>
  <title>Model</title>
  <meta http-equiv="content-type" content="text/html; charset=UTF-8" />
  <style type="text/css">
    .hspace { height: 2em }
    td,th {
       padding: 0 10px;
       border-bottom: 1px solid;
    }
    .selected { background: rgba(100,200,100,0.5) }
    .highlighted { background: rgba(200,100,100,0.5) }
   #heapgraph-container {
     height: 500px;
     width: 100%;
     border: 1px solid black;
   }
   svg {
     overflow: hidden;
     display: inline;
     width: inherit;
     height: inherit;
     min-width: inherit;
     min-height: inherit;
   }
  </style>
  <script src="http://ariutta.github.io/svg-pan-zoom/dist/svg-pan-zoom.min.js"></script>

</head>
<body>

  <script type="text/javascript">
    function forEachByTag(tag, callback) {
      var elements = document.getElementsByTagName(tag);
      for (var i = 0; i < elements.length; i++) {
        callback(elements[i]);
      }
    }
    function forEachByClass(cls, callback) {
      var elements = document.getElementsByClassName(cls);
      for (var i = 0; i < elements.length; i++) {
        callback(elements[i]);
      }
    }
    function iterateOverTableCells(col, fct) {
      forEachByTag('table', function(t) {
        for(var j = 1; j< t.rows.length; j++){
          if (t.rows[j].cells.length > col) {
            fct(t.rows[j].cells[col])
          }
        }
      });
    }
    function iterateOverNodes(fct) {
      forEachByClass('node', fct);
    }
    function nodeLabel(node) {
      return node.getElementsByTagName('text')[0].innerHTML;
    }
    function contains(s1, s2) {
      return s1.indexOf(s2) > -1;
    }
    function fillNode(node) {
      var elements = node.getElementsByTagName('polygon');
      for (var i = 0; i < elements.length; i++) {
        elements[i].style.fill = "rgba(100,250,100,0.7)";
      }
      elements = node.getElementsByTagName('ellipse');
      for (var i = 0; i < elements.length; i++) {
        elements[i].style.fill = "rgba(100,250,100,0.7)";
      }
    }
    function resetNode(node) {
      var elements = node.getElementsByTagName('polygon');
      for (var i = 0; i < elements.length; i++) {
        elements[i].style.fill = "none";
      }
      elements = node.getElementsByTagName('ellipse');
      for (var i = 0; i < elements.length; i++) {
        elements[i].style.fill = "none";
      }
    }
    function resetCells() {
      //clean the current highlight
      var elements = document.getElementsByClassName('selected');
      for (var i = 0; i < elements.length; i++) {
        elements[i].classList.remove('selected');
      }
      elements = document.getElementsByClassName('highlighted');
      for (var i = 0; i < elements.length; i++) {
        elements[i].classList.remove('highlighted');
      }
    }
    var lastHighlight = "";
    function highlight(terms){
      resetCells();
      if (terms === lastHighlight) {
        terms = "";
      }
      lastHighlight = terms;
      iterateOverNodes(function(n) {
        if (contains(terms, nodeLabel(n))) {
          fillNode(n);
        } else {
          resetNode(n);
        }
      });
    }
    var lastSelected = undefined;
    function highlightRelated(cell) {
      resetCells();
      if (cell === lastSelected) {
        highlight("");
        lastSelected = undefined;
      } else {
        highlight(cell.innerHTML);//TODO should expand the defs ???
        lastSelected = cell;
        iterateOverTableCells(0, function(c) {
          if (contains(c.innerHTML, cell.innerHTML)) {
            c.classList.add('highlighted');
          }
        });
        cell.classList.remove('highlighted');
        cell.classList.add('selected');
      }
    }
    function highlightNode(node) {
      resetCells();
      var l = nodeLabel(node);
      iterateOverTableCells(1, function(c) {
        if (contains(c.innerHTML, l)) {
          c.classList.add('highlighted');
        }
      });
      iterateOverTableCells(0, function(c) {
        if (contains(c.innerHTML, l)) {
          c.classList.add('highlighted');
        }
      });
      iterateOverNodes(resetNode);
      fillNode(node);
    }
    function setTooltip(){
      forEachByTag('table', function(t) {
        var lbl;
        for(var j = 1; j < t.rows.length; j++){
          var row = t.rows[j].cells;
          if (row.length > 1) {
            lbl = row[1].innerHTML.replace(/&lt;/g,'<').replace(/&gt;/g,'>');
          }
          if (lbl !== undefined) {
            row[0].title = lbl;
          }
        }
      });
    }
    window.onload=function() {
      iterateOverTableCells(1, function(c) { c.onclick=function(){ highlight(this.innerHTML); } });
      iterateOverTableCells(0, function(c) { c.onclick=function(){ highlightRelated(this); } });
      iterateOverNodes(function(n) { n.onclick=function(){ highlightNode(this); } });
      var PanZoomGraph = svgPanZoom("#heapgraph");
      setTooltip();
      document.body.ondragstart=function(){return false;};
      document.body.ondrop=function(){return false;};
    };
// Filter rows of the table
// Code from http://codepen.io/chriscoyier/pen/tIuBL
(function(document) {
    'use strict';

    var LightTableFilter = (function(Arr) {

        var _input;

        function _onInputEvent(e) {
            _input = e.target;
            var tables = document.getElementsByClassName(_input.getAttribute('data-table'));
            Arr.forEach.call(tables, function(table) {
                Arr.forEach.call(table.tBodies, function(tbody) {
                    Arr.forEach.call(tbody.rows, _filter);
                });
            });
        }

        function _filter(row) {
            var text = row.textContent.toLowerCase(), val = _input.value.toLowerCase();
            row.style.display = text.indexOf(val) === -1 ? 'none' : 'table-row';
        }

        return {
            init: function() {
                var inputs = document.getElementsByClassName('light-table-filter');
                Arr.forEach.call(inputs, function(input) {
                    input.oninput = _onInputEvent;
                });
            }
        };
    })(Array.prototype);

    document.addEventListener('readystatechange', function() {
        if (document.readyState === 'complete') {
            LightTableFilter.init();
        }
    });

})(document);

  </script>
  <div class="hspace"></div>
"""

footer = """\
  <div class="hspace"></div>
</body>
</html>
"""

def parse_model_file(fname):
    stack = {}
    data = {}
    nxt = {}
    nodes = set()
    with open(fname, 'r') as fin:
        for line in fin:
            if line.startswith('['):
                m = re.match("\[([^ ]*) : A (\d*)\]", line)
                var, addr = m.group(1), m.group(2)
                stack[var] = addr
            else:
                m = re.match("\((\d*), (\w*), (\w) (-?\d*)\)", line)
                nodes.add(m.group(1))
                if m.group(2) == "next":
                    nxt[m.group(1)] = m.group(4)
                elif m.group(2) == "data":
                    data[m.group(1)] = m.group(4)
                else:
                    print "Unknown field in file %s." % fname
                    #assert 0  # Unknown field
    return stack, data, nxt, nodes

def output_dot(fname, stack, data, nxt, nodes):
    # Calculate ids for heap and stack nodes
    ids = {}
    ids['0'] = 0  # Add null node manually
    counter = 1
    for n in nodes:
        ids[n] = counter
        counter += 1
    for s in stack.keys():
        ids[s] = counter
        counter += 1

    with open(fname, 'w') as f:
        f.write("digraph Model {\n")
        f.write("graph[rankdir=LR];\n")
        for n in nodes:
            f.write("  \"%d\" [shape=none, margin=0, label=<\n" % ids[n])
            f.write("    <table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n")
            f.write("      <tr><td><b>%s</b></td></tr>\n" % ("Node " + n))
            if n in data:
                f.write("      <tr><td><b>data = %s</b></td></tr>\n" % (data[n]))
            f.write("</table>\n>];\n")

        for var in stack.keys():
            f.write("  \"%d\" [label=\"%s\"];" % (ids[var], var))

        for n in nodes:
            f.write("\"%d\" -> \"%d\" [label=\"%s\", color=\"%s\"]\n" % (ids[n], ids[nxt[n]], "next", "black"))

        for var, val in stack.iteritems():
            f.write("\"%d\" -> \"%d\" [label=\"%s\", color=\"%s\"]\n" % (ids[var], ids[val], "", "black"))

        f.write("}\n")

def write_one_model(in_file_name, fout):
    stack, data, nxt, nodes = parse_model_file(in_file_name)
    output_dot("tmp.dot", stack, data, nxt, nodes)
    import subprocess
    svg_out = subprocess.check_output(["dot", "-Tsvg", "tmp.dot"])
    start_idx = svg_out.find("<svg")
    assert start_idx >= 0
    svg_out = svg_out[start_idx:]
    fout.write(svg_out)
    os.remove("tmp.dot")
        
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("in_files",
                        help="the _model txt files",
                        type=str,
                        nargs='+')
    parser.add_argument("-o",
                        help="output will be written to O.html (default: models.html)",
                        default="models",
                        type=str)
    args = parser.parse_args()

    with open(args.o + ".html", 'w') as f:
        f.write(header)
        for fname in args.in_files:
            f.write("\n<hr><h2>%s</h2>\n" % fname)
            write_one_model(fname, f)
        f.write(footer)

