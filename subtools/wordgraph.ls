Module wordgraph

use standard

use graph.word

use set.word

use svg2graph.word

Export drawgraph(arcs:seq.arc.word, set.word, set.word) seq.word
{From svg2graph.word}

function nodeTitle(word) seq.word ""

function node2text(a:word) seq.word [a]

function generatenode(a:set.word) word toword.cardinality.a 