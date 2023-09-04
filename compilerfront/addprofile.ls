Module addprofile

use seq.mytype

use encoding.parc2

use otherseq.parc2

use standard

use symbol

use set.arc.symbol

use graph.symbol

use otherseq.symbol

use set.symbol

use set.symdef

function %(a:arc.symbol) seq.word %.tail.a + %.head.a

function subaddprofile(sd:symdef, recursive:set.symbol) seq.symbol
{assert name.sym.sd /nin" testprofile" report" KL"+%.sym.sd+%.code.sd,}
for acc2 = empty:seq.symbol, sym ∈ code.sd
do
 if
  isconstantorspecial.sym
  ∨ isInternal.sym
  ∨ isFref.sym
  ∨ isGlobal.sym
  ∨ 
   isBuiltin.sym
   ∧ (name.sym ∉ "createthreadZ" ∨ n.acc2 ≤ 1 ∨ not.isFref.(n.acc2 - 1)_acc2)
 then
 acc2 + sym
 else if isBuiltin.sym then
  let functocall = (n.acc2 - 1)_acc2
  let offset = valueofencoding.encode.parc2(sym.sd, basesym.functocall) * 6 + (2 - 6),
   acc2 >> 3
   + [
    profiledata
    , Lit.0
    , Getfld.seqof.typeptr
    , Lit(offset + 2)
    , symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
    , symbol(internalmod, "bitcast", typeptr, typeint)
    , (n.acc2 - 1)_acc2
    , 1^acc2
    , sym
   ]
 else
  let offset = valueofencoding.encode.parc2(sym.sd, sym) * 6 + (2 - 6),
  acc2 + profileCallNR(offset, sym, n.code.sd + n.acc2, sym ∈ recursive),
acc2

Function addprofile(prg:set.symdef, libname:word) set.symdef
let recursive = asset.recursiveFunctions(toseq.prg, empty:set.symbol)
for acc = empty:set.symdef, sd ∈ toseq.prg
do
 if isPROFILE.sd ∧ not.isAbstract.module.sym.sd then
 acc + symdef4(sym.sd, subaddprofile(sd, recursive), paragraphno.sd, getOptionsBits.sd)
 else acc,
acc ∪ initProfileDefinition.libname

function profiledata symbol
symbol(moduleref."internallib $global", "profiledata", empty:seq.mytype, typeptr)

function profileCallNR(
 offset:int
 , callee:symbol
 , nextvar:int
 , recursive:boolean
) seq.symbol
let before = [
 symbol(internalmod, "clock", typeint)
 , Define(nextvar + 1)
 , symbol(internalmod, "spacecount", typeint)
 , Define(nextvar + 2)
 , callee
]
let after = [
 Local(nextvar + 1)
 , Local(nextvar + 2)
 , profiledata
 , Lit.0
 , Getfld.seqof.typeptr
 , Lit(offset + 2)
 , symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
 , symbol(moduleref."* tausupport", "profileUpdate", typeint, typeint, typeptr, typeint)
],
if recursive then
 adjust(offset, nextvar, 1)
 + before
 + adjust(offset, nextvar,-1)
 + [Start.typeint, Local.nextvar, Lit.0, EqOp, Br2(2, 1), Lit.0, Exit]
 + after
 + [Exit, EndBlock, Define.nextvar]
else before + after + Define.nextvar

function adjust(offset:int, nextvar:int, litvalue:int) seq.symbol
[profiledata, Lit.0, Getfld.seqof.typeptr]
 + Lit(offset + 5)
 + symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
 + Define(nextvar + 3)
 + [
 {get value and increment} Local(nextvar + 3)
 , Lit.0
 , Getfld.typeint
 , Lit.litvalue
 , PlusOp
 , Define.nextvar
]
 + [{store} Local(nextvar + 3), Local.nextvar, setSym.typeint, Define(nextvar + 3)]

type parc2 is caller:symbol, callee:symbol

function hash(p:parc2) int hash.callee.p + 1 + (hash.caller.p + 1)

function =(a1:parc2, b1:parc2) boolean callee.a1 = callee.b1 ∧ caller.a1 = caller.b1

function %(v:parc2) seq.word %.caller.v + %.callee.v

function initProfileDefinition(libname:word) set.symdef
let v = encodingdata:parc2
let data =
 for acc = empty:seq.symbol, p ∈ v
 do acc + Fref.caller.p + Fref.callee.p + [Lit.0, Lit.0, Lit.0, Lit.0],
  acc
  + Sequence(typeint, n.acc)
  + Define.1
  + Local.1
  + Lit.1
  + setSym.typeint
  + Lit.n.v
  + setSym.typeint
  + Define.2
  + [profiledata]
  + Local.1
  + setSym.typeptr,
asset.[
 symdef(symbol(moduleref.[libname, 1_"initialize"], "initProfile", typeptr), data, 0)
 , symdef(
  symbol(moduleref.[libname, 1_"initialize"], "profileData", typeptr)
  , [profiledata, Lit.0, Getfld.typeptr]
  , 0
 )
]

Function recursiveFunctions(s:seq.symdef, removein:set.symbol) seq.symbol
{OPTION XPROFILE}
for acc = removein, arcs = empty:set.arc.symbol, sd ∈ s
do
 if isAbstract.module.sym.sd then
 next(acc, arcs)
 else
  let calls =
   for acc2 = empty:set.symbol, sym ∈ code.sd
   do if isconstantorspecial.sym ∨ isInternal.sym then acc2 else acc2 + sym,
   acc2 \ acc,
  next(
   if isempty.calls then acc + sym.sd else acc
   , (for acc2 = arcs, x ∈ toseq.calls do acc2 + arc(sym.sd, x), acc2)
  ),
cyclenodes.newgraph.toseq.arcs

function removeSinksSources(g:graph.symbol) graph.symbol
let sinks = sinks.g
let remove = if isempty.sinks then sources.g else sinks,
if isempty.remove then g else removeSinksSources.subgraph(g, nodes.g \ asset.remove)

function cyclenodes(g:graph.symbol) seq.symbol
let tc = transitiveClosure.removeSinksSources.g
for acc = empty:seq.symbol, n ∈ toseq.nodes.tc
do if arc(n, n) ∈ arcs.tc then acc + n else acc,
acc 