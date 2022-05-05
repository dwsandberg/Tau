Module frontcmd

use baseTypeCheck

use standard

use symbol2

use graph.symbol

use set.symbol

use svg2graph.symbol

use graph.symbolref

use seq.symbolref

use set.symbolref

use seq.arc.symbol

use seq.arc.symbolref

use set.arc.symbolref


use seq.symbol

use set.symbol

use set.symdef

use symbol2

Function roots(s:midpoint)set.symbol
  for exports = empty:seq.symbol, m ∈ libmods.s do exports + exports.m /for(asset.exports)


function uses(toprocess:seq.symbol,org:set.symdef, new:set.symdef) set.symdef
for    newsym=empty:seq.symbol,newsd=new,   sym /in toprocess do
let t=lookup(new,symdef(sym,empty:seq.symbol,0))
 if not.isempty.t then   next(newsym,newsd)
 else
  let t2=lookup(org,symdef(sym,empty:seq.symbol,0))
  if isempty.t2 then 
      next(newsym,newsd+symdef(sym,empty:seq.symbol,0))
  else  
   next( for acc=newsym, sym2 /in code.t2_1 do
     if isspecial.sym2 then acc
     else if isconst.sym2 /and not.isrecordconstant.sym2 then
       if isFref.sym2 then  acc+basesym.sym2 else acc
     else  acc+sym2 /for(acc), newsd+t2_1)
 /for( if isempty.new then newsd else uses(toseq.asset.newsym,org,newsd))

Function front2(cf:midpoint, pass:seq.word, names:seq.word, ~n:seq.word, mods:seq.word
, ~mods:seq.word, samemodule:boolean, rootnames:seq.word, out:seq.word)seq.word
let prg=uses(toseq.roots.cf,prg.cf,empty:set.symdef)
for selected = empty:seq.symdef, root = empty:seq.symbol, sd ∈ toseq.prg do
let ss=sym.sd
  if(isempty.mods ∨ name.module.ss ∈ mods) ∧ (isempty.names ∨ name.ss ∈ names) ∧ name.ss ∉ ~n
 ∧ name.module.ss ∉ ~mods then
  next(selected + sd
  , if name.ss ∈ rootnames then root + ss else root
  )
 else next(selected, root)
/for(if out = "sym"then
 for txt = "", i ∈ selected do txt + " /p" + print.sym.i /for(txt)
else if out = "symdef"then
 for txt = "", sd1 ∈ selected do
    txt + " /p" + print.sym.sd1+print.code.sd1
 /for(txt)
else if out = "baseTypeCheck"then baseTypeCheck(toseq.prg,typedict.cf)
else if out = "resultCheck"then checkresults.toseq.prg
else  
  let syms=for acc=empty:set.symbol, sd5 /in selected do acc+sym.sd5 /for(acc)
 let g = 
  for acc = empty:seq.arc.symbol, sd1 ∈ selected do
    for acc2 = acc, h ∈ toseq(asset(code.sd1) ∩ syms)do
      if  sym.sd1=h  /or  samemodule ∧ (module.sym.sd1  = module.h) then acc2 else   acc2 + arc(sym.sd1, h)
    /for(acc2)
  /for(newgraph.acc)
  let g2 = 
  if not.isempty.root then
   for g2 = newgraph.empty:seq.arc.symbol, new = asset.root, i ∈[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]do
    let g3 = for g3 = g2, r ∈ toseq.new do g3 + toseq.arcstopredecessors(g, r)/for(g3)
    next(g3, nodes.g3 \ nodes.g2)
   /for(g2)
  else g
 if out = "text"then
  for txt = "txt", a ∈ toseq.arcs.g do txt + " /br" + print.tail.a + print.head.a /for(txt)
 else
  drawgraph.newgraph.toseq.arcs.g2) 

use seq.symdef

use set.symdef

use set.arc.symbol

function =(a:symdef,b:symdef) boolean sym.a=sym.b



Export drawgraph(graph.symbol)seq.word

Function generatenode(a:set.symbol)symbol Lit.cardinality.a

did not get error when result type of generatednode was seq.word!!!!!

Function node2text(a:symbol)seq.word[name.a]

Function nodeTitle(a:symbol)seq.word print.a

 /< command frontcmd front  />

 /< option 1 -library  /> Library to compile.

 /< option 1 -pass  /> pass of compile to run

 /< option * -n  /> list of symbol names to include

 /< option * -!n  /> list of symbol names to exclude

 /< option * -mods  /> list of modules to include

 /< option * -!mods  /> list of modules to exluded
 
 /< option f -within /> exclude arcs within module
 
 /< option * -rn  />  root names
 
 /< option 1 pretty baseTypeCheck sym symdef resultCheck-out  /> format of output  

-out sym will print list of symbols

-out symdef will print list of symbols and the code represented as a list of symbols

-out baseTypeCheck

-out resultCheck 

-out txt will print the arcs in the resulting graph rather than display the graph.