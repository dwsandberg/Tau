#!/bin/sh tau  stdlib  tools  front  library=  david -mods( david delta) #



Module frontcmd

use baseTypeCheck

use libraryModule

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

Function front(cf:compileinfo, pass:seq.word, names:seq.word, ~n:seq.word, mods:seq.word
, ~mods:seq.word,samemodule:boolean,rootnames:seq.word, out:seq.word)seq.word
for selected = empty:seq.symbolref, root = empty:seq.symbolref, idx = 1, ss ∈ symbolrefdecode.cf do
 if isconst.ss ∨ isspecial.ss then next(selected, root, idx + 1)
 else if(isempty.mods ∨ name.module.ss ∈ mods) ∧ (isempty.names ∨ name.ss ∈ names) ∧ name.ss ∉ ~n
 ∧ name.module.ss ∉ ~mods then
  next(selected + symbolref.idx
  , if name.ss ∈ rootnames then root + symbolref.idx else root
  , idx + 1
  )
 else next(selected, root, idx + 1)
/for({if out="test"then for txt="", i ∈ root do txt+" /p"+print.cf_i /for(txt)else}
if out = "sym"then
 for txt = "", i ∈ selected do txt + " /p" + print.cf_i /for(txt)
else if out = "symdef"then
 for txt = "", c ∈ code.cf do
  if c_1 ∈ selected then
   txt + " /p" + print.cf_(c_1)
   + for cc = "body", r ∈ c << 2 do cc + print.cf_r /for(cc)
  else txt
 /for(txt)
else if out = "baseTypeCheck"then baseTypeCheck.cf
else if out = "resultCheck"then checkresults.prg.cf
else
 let s = asset.selected
 let g = 
  for acc = empty:seq.arc.symbolref, c ∈ code.cf do
   if c_1 ∉ selected then acc
   else 
    for acc2 = acc, h ∈ toseq(asset(c << 2) ∩ s)do 
     if samemodule ∧ module.cf_(first.c) = module.cf_h then acc2 else acc2 + arc(first.c, h)
   /for(acc2)
  /for(newgraph.acc)
 let g2 = 
  if not.isempty.root then
   for g2 = newgraph.empty:seq.arc.symbolref, new = asset.root, i ∈[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]do
   let g3 = for g3 = g2, r ∈ toseq.new do g3 + toseq.arcstopredecessors(g, r)/for(g3)
   next(g3, nodes.g3 \ nodes.g2)
  /for(g2)
  else g
 if out = "text"then
  for txt = "txt", a ∈ toseq.arcs.g2 do txt + " /br" + print.cf_(tail.a) + print.cf_(head.a)/for(txt)
 else
  for acc = empty:seq.arc.symbol, c ∈ toseq.arcs.g2 do
   if tail.c = head.c then acc else acc + arc(cf_(tail.c), cf_(head.c))
  /for(drawgraph.newgraph.acc)/if /if /if /if /if)

function =(a:symbolref, b:symbolref)boolean toint.a = toint.b

Export drawgraph(graph.symbol)seq.word

Function generatenode(a:set.symbol)symbol Lit.cardinality.a

did not get error when result type of generatednode was seq.word!!!!!

Function node2text(a:symbol)seq.word[name.a]

Function nodeTitle(a:symbol)seq.word print.a

 /< command  frontcmd front  />

 /< option 1 -library  /> Library to compile.

 /< option 1 -pass  /> pass of compile to run

 /< option * -n  /> list of symbol names to include

 /< option * -!n  /> list of symbol names to exclude

 /< option * -mods  /> list of modules to include

 /< option * -!mods  /> list of modules to exluded
 
 /< option f -within /> exclude arcs within module
 
 /< option * -rn  />  root names
 
 /< option 1 pretty baseTypeCheck sym symdef resultCheck-out  /> format of output  /< block The comand"front out=pretty library 
=<Library>"will check the sematics and place one file for each module in directory tmp  />

-out sym will print list of symbols

-out symdef will print list of symbols and the code represented as a list of symbols

-out baseTypeCheck

-out resultCheck 

-out txt will print the arcs in the resulting graph rather than display the graph.