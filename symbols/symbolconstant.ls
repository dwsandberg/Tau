Module symbolconstant

use standard

use symbol

use otherseq.symbol

use sparseseq.symbol

use encoding.symbolconstant

use seq.symdef

use set.symdef

Export type:symbolconstant

Function seqelements(s:symbol)seq.symbol
if iswords.s then for acc = empty:seq.symbol, w ∈ worddata.s do acc + Word.w /for(acc)
else
 assert isrecordconstant.s report"constant code error" + %.s
 let code1 = fullconstantcode.s
 assert isSequence.last.code1 report"constant code error 21" + %.code1
 code1 >> 1

Function fullconstantcode(s:symbol)seq.symbol toseq.decode.to:encoding.symbolconstant(toint.name.s)

Function Constant2(args:seq.symbol)symbol symconst(addorder.symbolconstant.args, hasfref.args)

function hasfref(args:seq.symbol)boolean
for hasfref = false, sym ∈ args while not.hasfref do hasfref.sym /for(hasfref)

Function hash(s:seq.symbol)int
hash.for acc = "", e ∈ s do acc + worddata.e + name.module.e /for(acc)

type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function constantsymbols set.symdef
for acc = empty:set.symdef, i = 1, p ∈ encodingdata:symbolconstant do next(acc + symdef(symconst(i, hasfref.toseq.p), toseq.p, 0), i + 1)/for(acc)

function map(map0:seq.symbol, prg:seq.symdef)seq.symbol
for map = map0, todo = empty:seq.symdef, sd ∈ prg do
 if isrecordconstant.sym.sd then
  let i = toint.name.sym.sd
  let newmap = 
   for acc = empty:seq.symbol, ok = true, sym ∈ code.sd
   while ok
   do
    if isrecordconstant.sym then
     let mapvalue = map_(toint.name.sym)
     next(acc + mapvalue, isrecordconstant.mapvalue)
    else next(acc + sym, ok)
   /for(if ok then replaceS(map, i, [Constant2.acc])else empty:seq.symbol)
  if isempty.newmap then next(map, todo + sd)else next(newmap, todo)
 else next(map, todo)
/for(
 if isempty.todo then map
 else
  assert length.todo < length.prg
  report"ill formed program"
  + for txt = "", sd2 ∈ todo do txt + " /p" + %.sym.sd2 + %.code.sd2 /for(txt)
  map(map, todo))

Function renumberconstants(prg:seq.symdef)seq.symdef
let map = map(sparseseq.Lit.0, prg)
for newprg = empty:seq.symdef, sd ∈ prg do
 if isrecordconstant.sym.sd then newprg
 else
  let newcode = 
   for acc = empty:seq.symbol, changed = false, sym ∈ code.sd do
    if isrecordconstant.sym then next(acc + map_(toint.name.sym), true)else next(acc + sym, changed)
   /for(if changed then acc else code.sd)
  newprg + symdef(sym.sd, newcode, paragraphno.sd)
/for(newprg) 