module bitcodesupport

use UTF8

use llvmconstants

use standard

use seq.word

use seq.seq.int

Function ABBROPFixed int 1

Function ABBROPVBR int 2

Function ABBROPArray int 3

Function ABBROPChar6 int 4

Function ABBROPBlob int 5

Function ENDBLOCK int 0

Function ENTERSUBBLOCK int 1

Function DEFINEABBREV int 2

Function UNABBREVRECORD int 3

Function SETBID int 1

Function printtype(s:seq.seq.int, i:int, llvm:boolean) seq.word
if i = 1 then
 "conststype"
else
 {if i = 2 then" profiletype" else}
 let a = s_(i + 2)
 let tp = typeop.a_1,
 if tp = INTEGER then
  [merge("i" + toword.a_2)]
 else if tp = ARRAY then
  "array (" + toword.a_2 + "," + printtype(s, a_3, llvm) + ")"
 else if tp = POINTER then
  if llvm then "$(printtype(s, a_2, llvm)) *" else "ptr.$(printtype(s, a_2, llvm))"
 else if tp = FUNCTION then
  "function.[
   $(for acc = "", @e ∈ subseq(a, 3, length.a) do
   acc + printtype(s, @e, llvm) + ","
  /do acc >> 1)
   ]"
 else if tp = TVOID then "VOID" else if tp = DOUBLE then "double" else "?"

Function printabbr(a:seq.int) seq.word
for acc = "", plain = true, code ∈ a do
 if plain then
  next(acc + %.code, false)
 else if code = 0 then
  next(acc + "Lit", true)
 else if code = ABBROPFixed then
  next(acc + "Fixed", true)
 else if code = ABBROPVBR then
  next(acc + "VBR", true)
 else if code = ABBROPArray then
  next(acc + "Array", false)
 else if code = ABBROPChar6 then
  next(acc + "Char6", false)
 else if code = ABBROPBlob then
  next(acc + "BLob", false)
 else
  next(acc + "illegal", false)
/do acc

Function number(s:seq.seq.word) seq.word
for txt = "", label = 0, p ∈ s do
 next(txt + "{$(label)} $(p) /br,", label + 1)
/do txt >> 2

use otherseq.int

Function printrecord(id:blockop, a:seq.int) seq.word
if id = VALUESYMTABLE then
 "function" + encodeword.tocharseq.subseq(a, 3, length.a) + "int" + toword.a_2
else if a_1 = -1 then
 "[-1, $(decode.blockop.a_2), $(%(",", subseq(a, 2, length.a)) >> 1)]"
else if a_1 = -2 then
 printabbr.a
else if id = INFOBLOCK ∧ length.a = 2 ∧ a_1 = SETBID then
 "[SETBID, $(decode.blockop.a_2)]"
else
 let code = a_1
 let recordtype = 
  if id = MODULE then
   decode.moduleop.code
  else if id = TYPES then
   decode.typeop.code
  else if id = FUNCTIONBLK then
   decode.instop.code
  else if id = CONSTANTS then decode.constop.code else [toword.code]
 ,
 if length.a = 1 then
  "[toint.$(recordtype)]"
 else
  "[toint.$(recordtype), $(%(",", subseq(a, 2, length.a)) >> 1)]" 