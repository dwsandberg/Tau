Module addprofile

use bits

use seq.byte

use seq.mytype

use encoding.parc2

use seq.parc2

use standard

use symbol

use otherseq.arc.symbol

use set.arc.symbol

use graph.symbol

use otherseq.symbol

use set.symbol

use symbol2

use otherseq.symdef

use set.symdef

use textio

function %(sd:symdef) seq.word %.sym.sd + %.code.sd

function %(a:arc.symbol) seq.word %.tail.a + %.head.a

Function addprofile(prg:set.symdef) set.symdef
let recusive = recursiveFunctions(toseq.prg, empty:set.symbol)
for acc = empty:set.symdef, sd ∈ toseq.prg do
 if isPROFILE.sd ∧ not.isAbstract.module.sym.sd then
  for acc2 = empty:seq.symbol, sym ∈ code.sd do
   if isconstantorspecial.sym ∨ isInternal.sym ∨ isBuiltin.sym then
    acc2 + sym
   else
    acc2
    + if sym ∈ recusive then
     profileCallR(sym.sd, sym, length.code.sd)
    else
     profileCallNR(sym.sd, sym, length.code.sd)
  /for (acc + symdef4(sym.sd, acc2, paragraphno.sd, getOptionsBits.sd))
 else
  acc
/for (acc ∪ initProfileDefinition ∪ prg)

function profiledata symbol
symbol(moduleref."internallib $global", "profiledata", empty:seq.mytype, typeptr)

function profileCallNR(caller:symbol, callee:symbol, nextvar:int) seq.symbol
[symbol(internalmod, "clock", typeint)
 , Define.nextvar
 , symbol(internalmod, "spacecount", typeint)
 , Define(nextvar + 1)
 , callee
 , Local.nextvar
 , Local(nextvar + 1)
 , profiledata
 , Lit.0
 , Getfld.seqof.typeptr
 , Lit(addprofile2(caller, callee) + 2)
 , symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
 , symbol(moduleref."* tausupport", "profileUpdate", typeint, typeint, typeptr, typeptr)
 , Define.nextvar]

function addprofile2(caller:symbol, callee:symbol) int
let t = valueofencoding.encode.parc2(caller, callee)
t * 6 + (2 - 6)

function adjust(offset:int, nextvar:int, litvalue:int) seq.symbol
[profiledata, Lit.0, Getfld.seqof.typeptr] + Lit(offset + 5)
+ symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
+ Define.nextvar
+ [Local.nextvar, Lit.0, Getfld.typeint, Define(nextvar + 1)]
+ [{increment and store} Local.nextvar
 , Local(nextvar + 1)
 , Lit.litvalue
 , PlusOp
 , setSym.typeint
 , Define.nextvar]

function profileCallR(caller:symbol, callee:symbol, nextvar:int) seq.symbol
let offset = addprofile2(caller, callee)
adjust(offset, nextvar, 1) + [symbol(internalmod, "clock", typeint), Define.nextvar]
+ [symbol(internalmod, "spacecount", typeint), Define(nextvar + 2)]
+ callee
+ Start.resulttype.callee
+ Local(nextvar + 1)
+ Lit.0
+ EqOp
+ Br2(1, 2)
+ Lit.0
+ Exit
+ [Local.nextvar
 , Local(nextvar + 2)
 , profiledata
 , Lit.0
 , Getfld.seqof.typeptr
 , Lit(addprofile2(caller, callee) + 2)
 , symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
 , symbol(moduleref."* tausupport", "profileUpdate", typeint, typeint, typeptr, typeptr)
 , Define.nextvar
 , Lit.0
 , Exit]
+ EndBlock
+ Define.nextvar
+ adjust(offset, nextvar,-1)

type parc2 is caller:symbol, callee:symbol

function hash(p:parc2) int hash.callee.p + 1 + (hash.caller.p + 1)

function =(a:parc2, b:parc2) boolean callee.a = callee.b ∧ caller.a = caller.b

function initProfileDefinition set.symdef
let v = encodingdata:parc2
let data = 
 for acc = empty:seq.symbol, p ∈ v do
  acc + Fref.caller.p + Fref.callee.p + [Lit.0, Lit.0, Lit.0, Lit.0]
 /for (
  acc + Sequence(typeint, length.acc) + Define.1 + Local.1 + Lit.1 + setSym.typeint
  + Lit.length.v
  + setSym.typeint
  + Define.2
  + [profiledata]
  + Local.1
  + setSym.typeptr
 )
asset.[symdef(symbol(moduleref."* tausupport", "initProfile", typeptr), data, 0)
 , symdef(symbol(moduleref."* profile", "profileData", typeptr)
  , [profiledata, Lit.0, Getfld.typeptr]
  , 0)
 , symdef(symbol(moduleref."* profile", "????", seqof.typebyte), empty:seq.symbol, 0)]

Function recursiveFunctions(s:seq.symdef, removein:set.symbol) seq.symbol
{OPTION PROFILE}
for acc = removein, arcs = empty:set.arc.symbol, sd ∈ s do
 if isAbstract.module.sym.sd then
  next(acc, arcs)
 else
  let calls = 
   for acc2 = empty:set.symbol, sym ∈ code.sd do
    if isconstantorspecial.sym ∨ isInternal.sym then acc2 else acc2 + sym
   /for (acc2 \ acc)
  next(if isempty.calls then acc + sym.sd else acc
   , for acc2 = arcs, x ∈ toseq.calls do acc2 + arc(sym.sd, x) /for (acc2))
/for (cyclenodes.newgraph.toseq.arcs)

function removeSinksSources(g:graph.symbol) graph.symbol
let sinks = sinks.g
let remove = if isempty.sinks then sources.g else sinks
if isempty.remove then g else removeSinksSources.subgraph(g, nodes.g \ asset.remove)

function cyclenodes(g:graph.symbol) seq.symbol
let tc = transitiveClosure.removeSinksSources.g
for acc = empty:seq.symbol, n ∈ toseq.nodes.tc do
 if arc(n, n) ∈ arcs.tc then acc + n else acc
/for (acc)

/function removeSelf (g:graph.symbol) graph.symbol for acc = empty:set.arc.symbol, a ∈ toseq.arcs
.g do if tail.a = head.a then acc+a else acc /for (deletearcs (g, acc)) 