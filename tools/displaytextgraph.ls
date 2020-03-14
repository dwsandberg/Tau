Module displaytextgraph

use barycenter.seq.word

use display

use displaygraph.seq.word

use graph.seq.word

use ipair.seq.word

use otherseq.word

use seq.arcinfo.seq.word

use seq.word

use set.seq.word

use stdlib

use svggraph.seq.word

Function display(z2:seq.arcinfo.seq.word)seq.word"&{ noformat" + displaygraph(defaultcontrol, z2) + "&}"

Function arcinfo(tail:seq.word, head:seq.word, arclabel:seq.word)arcinfo.seq.word
 arcinfo(arc(tail, head), arclabel, displaywidth(chrwidths.defaultcontrol, arclabel))

function assignwidths(control:prettycontrol, p:nodeinfo.seq.word)nodeinfo.seq.word
 nodeinfo(n.p, x.p, y.p, displaywidth(chrwidths.control, n.p), seperation.p)

function ?(a:ipair.seq.word, b:ipair.seq.word)ordering index.b ? index.a

function generatenode(s:set.seq.word)seq.word [ toword.cardinality.s]

function ?(a:nodeinfo.seq.word, b:nodeinfo.seq.word)ordering n.a ? n.b

function nodetotext(a:seq.word)seq.word a