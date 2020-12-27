Module displaytextgraph

use display

use standard

use otherseq.word

use seq.arcinfo.seq.word

use barycenter.seq.word

use displaygraph.seq.word

use graph.seq.word

use ipair.seq.word

use set.seq.word

use svggraph.seq.word

use seq.word

Function display(z2:seq.arcinfo.seq.word)seq.word" &{ noformat" + displaygraph(charwidths, z2) + " &}"

Function arcinfo(tail:seq.word, head:seq.word, arclabel:seq.word)arcinfo.seq.word arcinfo(arc(tail, head), arclabel, displaywidth(charwidths, arclabel))

function assignwidths(control:characterwidths, p:nodeinfo.seq.word)nodeinfo.seq.word
 nodeinfo(n.p, x.p, y.p, displaywidth(control, n.p), seperation.p)

function ?(a:ipair.seq.word, b:ipair.seq.word)ordering index.b ? index.a

function generatenode(s:set.seq.word)seq.word [ toword.cardinality.s]

function ?(a:nodeinfo.seq.word, b:nodeinfo.seq.word)ordering n.a ? n.b

function nodetotext(a:seq.word)seq.word a