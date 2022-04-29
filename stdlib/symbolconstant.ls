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


 
Function buildargs(codein:seq.symbol) seq.int
 if  not.for ok=true,sym /in subseq(codein,1,20) do isconst.sym  
  /or isSequence.sym /or isRecord.sym
  /for(ok) then empty:seq.int
  else 
  for  ok=true,stk = empty:stack.int, sym ∈ codein while ok do
    if iswordseq.sym then
   let a = for acc = empty:seq.int, @e ∈ worddata.sym  do acc + hash.@e /for(acc)
  next(ok,push(stk, bitcast:int(toptr.a)))
  else if isword.sym then 
     next(ok,push(stk, hash.wordname.sym))
   else if isIntLit.sym ∨ isRealLit.sym then next(ok,push(stk, value.sym))
  else if sym = Littrue then next(ok,push(stk, 1))
  else if sym = Litfalse then next(ok,push(stk, 0))
  else if isrecordconstant.sym then 
     let t=buildargs(fullconstantcode.sym)
    next(not.isempty.t,if isempty.t then push(stk,0) else push(stk,first.t))   
  else if isSequence.sym then 
  let nopara = nopara.sym
   if length.toseq.stk < nopara.sym then next(false,stk) else
   next(ok,push(pop(stk, nopara), bitcast:int(toptr.packed.top(stk, nopara))))
  else { if isRecord.sym then
   let nopara = nopara.sym
    if length.toseq.stk < nopara.sym then next(false,stk) else
     next(ok,push(pop(stk, nopara), 
     bitcast:int(set(set(toptr.packed.top(stk, nopara), 0), nopara))))
  else }next(false,stk)
 /for( if ok then toseq.stk else empty:seq.int)
 
Function seqelements(s:symbol)seq.symbol
assert isrecordconstant.s report"constant code error" + print.s  
let code1 = fullconstantcode.s
assert isSequence.last.code1 report "constant code error 21" + print.code1  
 code1 >> 1 

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

Function constantsymbols set.symdef
for acc = empty:set.symdef, i=1,p ∈ encodingdata:symbolconstant do 
next(acc + symdef(symconst.i, toseq.p),i+1)/for(acc) 