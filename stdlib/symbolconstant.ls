Module symbolconstant

use standard

use symbol

use seq.mytype

use seq.symbol

use encoding.symbolconstant

use set.symdef

use stack.int

use bitcast:seq.int

use bitcast:int

use seq.int

use tausupport

Function buildargs2(codein:seq.symbol) seq.int
  { resulting stack will have too many elements if error is encountered }
  let error=1
  for stk = empty:stack.int, sym ∈ removeconstantcode.codein  do
  let nopara = nopara.sym
  if not.isconst.sym /or isFref.sym then push(push(stk,error),error)
  else if isword.sym then 
     push(stk, hash.wordname.sym)
  else if iswordseq.sym then
   let a = for acc = empty:seq.int, @e ∈ worddata.sym do acc + hash.@e /for(acc)
  push(stk, bitcast:int(toptr.a))
  else if isIntLit.sym ∨ isRealLit.sym then push(stk, value.sym)
  else if sym = Littrue then push(stk, 1)
  else if sym = Litfalse then push(stk, 0)
  else if isSequence.sym then push(pop(stk, nopara), bitcast:int(toptr.packed.top(stk, nopara)))
  else if isrecordconstant.sym then 
     let t=buildargs2(fullconstantcode.sym)
     if  length.t =1  then push(stk,first.t) else push(push(stk,error),error)  
  else if isRecord.sym then
   push(pop(stk, nopara), bitcast:int(set(set(toptr.packed.top(stk, nopara), 0), nopara)))
  else push(push(stk,error),error)
 /for( toseq.stk)
 

Function constantcode(s:symbol)seq.symbol
assert isrecordconstant.s report"constant code error" + print.s  
let code1 = fullconstantcode.s
if isSequence.last.code1 then[Lit.0, Lit.nopara.last.code1] + code1 >> 1 
else code1 >> 1

function fullconstantcode(s:symbol)seq.symbol
toseq.decode.to:encoding.symbolconstant(toint.name.s)

Function Constant2(p:set.symdef, args:seq.symbol)symbol
let testsym = symconst.nextencoding.symbolconstant.empty:seq.symbol
let a = lookup(p, symdef(testsym, args))
if not.isempty.a then
 let discard = encode.symbolconstant.code.a_1
 Constant2(p, args)
else symconst.addorder.symbolconstant.args

Function hash(s:seq.symbol)int
hash.for acc = "", e ∈ s do acc + worddata.e + name.module.e /for(acc)

function assignencoding(a:symbolconstant)int nextencoding.a

Export type:symbolconstant

type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function removeconstantcode(s:seq.symbol)seq.symbol
for acc = empty:seq.symbol, @e ∈ s do
 acc
 + if isrecordconstant.@e then removeconstantcode.fullconstantcode.@e else[@e]
/for(acc)

Function constantsymbols set.symdef
for acc = empty:set.symdef, i=1,p ∈ encodingdata:symbolconstant do 
next(acc + symdef(symconst.i, toseq.p),i+1)/for(acc) 