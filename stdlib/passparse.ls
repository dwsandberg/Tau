module passparse

use mytype

use parse

use passsymbol

use standard

use symbol

use symboldict

use typedict

use words

use seq.findabstractresult

use set.modref

use otherseq.mytype

use seq.mytype

use set.mytype

use set.passsymbols

use set.passtypes

use encoding.symbol

use graph.symbol

use seq.symbol

use set.symbol

use seq.symdef

use set.symdef

use seq.symtextpair

use set.word

use seq.seq.mytype

use seq.arc.symbol

use set.arc.symbol

use graph.seq.word

function abstractarcs(s:seq.symdef)seq.arc.symbol
for outer = empty:seq.arc.symbol, p ∈ s do
 let sym = sym.p
 for arcs = outer, codesym ∈ code.p do
  if isspecial.codesym ∨ not.isabstract.module.codesym ∨ sym = codesym ∨ isBuiltin.codesym then arcs
  else if inModFor.codesym then
   if name.codesym ∈ "name for"then arcs
   else arcs + arc(sym, indexsymbol.resulttype.codesym)
  else arcs + arc(sym, codesym)
 /for(arcs)
/for(outer)

function print(a:arc.symbol)seq.word print.tail.a + print.head.a

function removesinks(sinkstokeep:set.symbol, g:graph.symbol, toprocess:seq.symbol)seq.arc.symbol
{removes sinks that are not unbound and parameter of module is typeT}
{do a transitiveClosure and only keep arcs whose head is a sink}
{looking for relation of function to the unbound functions it can call.This are not quite yet that relation. }
for keep = sinkstokeep, pred = empty:set.symbol, g2 = g, n ∈ toprocess do
 if isunbound.n ∨ para.module.n ≠ typeT then next(keep + n, pred, g2)
 else next(keep, pred ∪ predecessors(g2, n), deletenode(g2, n))
/for(let newsinks = 
 for acc = empty:seq.symbol, p ∈ toseq.pred do if outdegree(g, p) = 0 then acc + p else acc /for(acc)
if isempty.newsinks then
 for acc = empty:seq.arc.symbol, a ∈ toseq.arcs.transitiveClosure.g2 do if head.a ∈ keep then acc + a else acc /for(acc)
else removesinks(keep, g2, newsinks)/if)

Function compile(allmods:set.passsymbols
, modlist:set.passsymbols
, lib:word
, src:seq.seq.word
, textmode:boolean
, requireUnbound:set.symdef
)seq.symdef
let mode=if textmode then "text"_1 else "body"_1
for prg = empty:seq.symdef, m ∈ toseq.modlist do
 let z = commoninfo("", modname.m, lib, typedict.m, mode)
 let partdict = formsymboldict(allmods, m, requireUnbound, mode)
 for acc = empty:seq.symdef, p ∈ text.m do
  if first.text.p ∈ "Builtin builtin"then
   if issimple.module.sym.p then acc + symdef(sym.p, addcommentoptions(text.p, empty:seq.symbol))
   else
    let sym = sym.p
    acc
    + symdef(sym.p
    , for code = empty:seq.symbol, @e ∈ arithseq(nopara.sym.p, 1, 1)do code + Local.@e /for(code)
    + [if issimplename.sym then symbol(builtinmod.typeT, [wordname.sym], paratypes.sym, resulttype.sym)
    else symbol4(builtinmod.typeT, wordname.sym, (nametype.sym)_1, paratypes.sym, resulttype.sym)
    ]
    )
  else
   assert first.text.p ∈ "Function function"report text.p
   let b = parse(src_(paragraphno.p), partdict, z)
   acc + symdef(sym.p, addcommentoptions(text.p, code.b), paragraphno.p)
 /for(prg + acc)
/for(prg)

function addcommentoptions(s:seq.word, code:seq.symbol)seq.symbol
let a = getheader.s
if subseq(s, length.a, length.a + 1) = "{OPTION"then
 for acc = "", w ∈ subseq(s, length.a + 2, length.s)
 while w ∉ "{}"
 do if w ∈ "PROFILE STATE COMPILETIME NOINLINE INLINE"then acc + w else acc
 /for(if isempty.s then code else addoption(code, acc)/if)
else code

/Function passparse(abstractmods:set.passsymbols
, simplemods:set.passsymbols
, lib:word
, prg1:seq.symdef
, src:seq.seq.word
, mode:word
)set.symdef
let allmods = abstractmods ∪ simplemods
let prga = compile(allmods, abstractmods, lib, src, mode, empty:set.symdef)
let requireUnbound=buildrequires(prga + prg1)
let prg = compile(allmods, simplemods, lib, src, mode, requireUnbound)
asset.{prescan2.}(prga + prg1 + prg)

Function buildrequires(prg:seq.symdef ) set.symdef
let g3 = newgraph.abstractarcs( prg)
{graph g3 has three kinds of sinks.1:is unbound and module parameter is T 2:is not unbound and module parameter is T 3:module 
parameter is not T examples:otherseq.T:=(T, T)boolean ; otherseq.T:step(arithmeticseq.T)T ; otherseq.sparseele 
.T:binarysearch(seq.sparseele.T)}
let sinks = asset.sinks.g3
let g4 = newgraph.removesinks(empty:set.symbol, g3, toseq.sinks)
{change many-to-one relation defined by arcs in g4 into format of set.symdef}
 if isempty.arcs.g4 then empty:set.symdef
 else
  for acc = empty:set.symdef, last = Lit.0, list = empty:seq.symbol, a ∈ toseq.arcs.g4 do
   let list0 = if last ≠ tail.a then empty:seq.symbol else list
   let newlist = if isunbound.head.a then list0 + head.a else list0
   let newacc = 
    if last ≠ tail.a then if isempty.list then acc else acc + symdef(last, list)
    else acc
   next(newacc, tail.a, newlist)
  /for(if isempty.list then acc else acc + symdef(last, list)/if)

Function prescan2(s:seq.symdef)seq.symdef  
{ removes name from locals and change length and getseqtype to GetSeqLength and GetSeqType }
for acc = empty:seq.symdef, p ∈ s do
 for result = empty:seq.symbol, sym ∈ code.p do
  if islocal.sym then result + Local.value.sym
  else if isdefine.sym then result + Define.value.sym
  else
   result
   + if isBuiltin.sym then
    if name.sym ∈ "length"then GetSeqLength
    else if name.sym ∈ "getseqtype"then GetSeqType else sym
   else sym
 /for(acc + symdef(sym.p, result))
/for(acc) 