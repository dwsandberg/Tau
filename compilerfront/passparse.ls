Module passparse

use seq.mytype

use parser

use passsymbol

use set.passsymbols

use standard

use symbol

use set.arc.symbol

use graph.symbol

use seq.symbol

use set.symbol

use symboldict

use set.symdef

function abstractarcs(s:seq.symdef) seq.arc.symbol
for outer = empty:seq.arc.symbol, p ∈ s
do
 let sym = sym.p
 for arcs = outer, codesym ∈ code.p
 do
  if isspecial.codesym ∨ not.isAbstract.module.codesym ∨ sym = codesym ∨ isBuiltin.codesym then
  arcs
  else if inModFor.codesym then
   if name.codesym ∈ "name for" then
   arcs
   else arcs + arc(sym, indexsymbol.resulttype.codesym)
  else arcs + arc(sym, codesym)
 ,
 arcs
,
outer

function removesinks(
 sinkstokeep:set.symbol
 , g:graph.symbol
 , toprocess:seq.symbol
) seq.arc.symbol
{removes sinks that are not unbound and parameter of module is typeT /br do a transitiveClosure and only keep arcs whose head is a sink
 /br looking for relation of function to the unbound functions it can call.This are not quite yet that relation. }
for keep = sinkstokeep, pred = empty:set.symbol, g2 = g, n ∈ toprocess
do
 if isunbound.n ∨ para.module.n ≠ typeT then
 next(keep + n, pred, g2)
 else next(keep, pred ∪ predecessors(g2, n), deletenode(g2, n))
let newsinks =
 for acc = empty:seq.symbol, p ∈ toseq.pred do if outdegree(g, p) = 0 then acc + p else acc,
 acc
,
if isempty.newsinks then
 for acc = empty:seq.arc.symbol, a ∈ toseq.arcs.transitiveClosure.g2
 do if head.a ∈ keep then acc + a else acc,
 acc
else removesinks(keep, g2, newsinks)

Function compile(
 allmods:set.passsymbols
 , modlist:set.passsymbols
 , lib:word
 , src:seq.seq.word
 , textmode:boolean
 , requireUnbound:set.symdef
) seq.symdef
{OPTION PROFILE}
let mode = if textmode then 1_"text" else 1_"body"
for prg = empty:seq.symdef, m ∈ toseq.modlist
do
 let partdict = formsymboldict(allmods, m, requireUnbound, mode)
 for acc = empty:seq.symdef, p ∈ srclink.m
 do
  let symsrc = (paragraphno.p)_src,
   if 1_symsrc ∈ "Builtin builtin" then
    if isSimple.module.sym.p then
    acc + symdef4(sym.p, empty:seq.symbol, paragraphno.p, commentoptions(symsrc, nopara.sym.p))
    else
     let sym = sym.p
     for code = empty:seq.symbol, @e ∈ arithseq(nopara.sym.p, 1, 1) do code + Local.@e,
      acc
      + symdef(
       sym.p
       ,
        code
        + [
         if issimplename.sym then
         symbol(builtinmod.typeT, [wordname.sym], paratypes.sym, resulttype.sym)
         else symbol4(builtinmod.typeT, wordname.sym, 1_nametype.sym, paratypes.sym, resulttype.sym)
        ]
       , 0
      )
   else if 1_symsrc ∈ "Export" then
   acc
   else
    assert 1_symsrc ∈ "Function function" report symsrc
    let dict = symboldict(syms.partdict, req.partdict)
    let code = parser(symsrc, dict, typedict.m, textmode),
    acc + symdef4(sym.p, code, paragraphno.p, commentoptions(symsrc, nopara.sym.p))
 ,
 prg + acc
,
prg

Function addExportOptions(
 modlist:set.passsymbols
 , prgin:set.symdef
 , src:seq.seq.word
) set.symdef
for prg = prgin, m ∈ toseq.modlist
do
 for acc = prg, p ∈ srclink.m
 do
  let symsrc = (paragraphno.p)_src,
   if 1_symsrc ∈ "Export" then
    let sd = getSymdef(acc, sym.p),
     if isempty.sd then
     acc
     else
      symdef4(
       sym.p
       , code.1_sd
       , paragraphno.1_sd
       , commentoptions(symsrc, nopara.sym.p) + getOptions.1_sd
      )
      ∪ acc
   else acc
 ,
 acc
,
prg

function commentoptions(s:seq.word, nopara:int) seq.word
let s0 = s << (if nopara = 0 then 0 else findindex(s, 1_")"))
let s1 = s0 << findindex(s0, 1_"{"),
if isempty.s1 ∨ 1_s1 ∉ "OPTION ENTRYPOINT" then
""
else
 for acc = "", w ∈ s1
 while w ∉ "{} /br"
 do if w ∈ "PROFILE STATE COMPILETIME NOINLINE INLINE ENTRYPOINT" then acc + w else acc,
 acc

Function buildrequires(prg:seq.symdef) set.symdef
let g3 = newgraph.abstractarcs.prg
{graph g3 has three kinds of sinks./br 1:is unbound and module parameter is T
 /br 2:is not unbound and module parameter is T
 /br 3:module parameter is not T
 /br examples:otherseq.T:= (T, T) boolean ; otherseq.T:step (arithmeticseq.T) T ;
 /br otherseq.sparseele.T:binarysearch (seq.sparseele.T)}
let sinks = asset.sinks.g3
let g4 = newgraph.removesinks(empty:set.symbol, g3, toseq.sinks)
{change many-to-one relation defined by arcs in g4 into format of set.symdef}
if isempty.arcs.g4 then
empty:set.symdef
else
 for acc = empty:set.symdef, last = Lit.0, list = empty:seq.symbol, a ∈ toseq.arcs.g4
 do
  let list0 = if last ≠ tail.a then empty:seq.symbol else list
  let newlist = if isunbound.head.a then list0 + head.a else list0
  let newacc = if last ≠ tail.a then if isempty.list then acc else acc + symdef(last, list, 0) else acc,
  next(newacc, tail.a, newlist)
 ,
 if isempty.list then acc else acc + symdef(last, list, 0) 