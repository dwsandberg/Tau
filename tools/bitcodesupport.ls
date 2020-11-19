#!/usr/local/bin/tau

/run printbitcodes test1

run runcode test2

run printbitcodes test1

run bitcodesupport generatecode

module bitcodesupport

use UTF8

use encoding.seq.char

use seq.seq.int

use llvmconstants

use stdlib

use seq.word

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

Function printtype(s:seq.seq.int, i:int)seq.word
 if i = 1 then"conststype"
 else if i = 2 then"profiletype"
 else
  let a = s_(i + 2)
  let tp = typeop.a_1
   if tp = INTEGER then [ merge("i" + toword.a_2)]
   else if tp = ARRAY then
   "array(" + toword.a_2 + "," + printtype(s, a_3)
    + ")"
   else if tp = POINTER then"ptr." + printtype(s, a_2)
   else if tp = FUNCTION then
   "function.[" + @(seperator(","), printtype(s),"", subseq(a, 3, length.a))
    + "]"
   else if tp = TVOID then"VOID"else if tp = DOUBLE then"double"else"?"

Function printabbr(a:seq.int)seq.word [ toword.a_1] + printabbr(2,"", a)

function printabbr(i:int, result:seq.word, a:seq.int)seq.word
 if i > length.a then result
 else if i = 1 then printabbr(i + 1, result + toword.a_i, a)
 else
  let code = a_i
   if code = 0 then
   printabbr(i + 2, result + "Lit" + toword.a_(i + 1), a)
   else if code = ABBROPFixed then
   printabbr(i + 2, result + "Fixed" + toword.a_(i + 1), a)
   else if code = ABBROPVBR then
   printabbr(i + 2, result + "VBR" + toword.a_(i + 1), a)
   else if code = ABBROPArray then printabbr(i + 1, result + "Array", a)
   else if code = ABBROPChar6 then printabbr(i + 1, result + "Char6", a)
   else if code = ABBROPBlob then printabbr(i + 1, result + "BLob", a)
   else printabbr(i + 1, result + "illegal", a)

Function number(s:seq.seq.word, i:int, startlabel:int)seq.word number(s, i, startlabel,"")

function number(s:seq.seq.word, i:int, startlabel:int, result:seq.word)seq.word
 if i > length.s then result
 else
  let new =(if isempty.result then""else" &br,") + "//" + toword.startlabel + "//"
  + s_i
   number(s, i + 1, startlabel + 1, result + new)

Function printrecord(blockid:int, a:seq.int)seq.word
 let id = blockop.blockid
  if id = VALUESYMTABLE then
  "function" + encodeword.tocharseq.subseq(a, 3, length.a) + "int" + toword.a_2
  else if a_1 = -1 then
  "[-1," + decode.blockop.a_2 + ","
   + @(seperator.",", toword,"", subseq(a, 2, length.a))
   + "]"
  else if a_1 = -2 then printabbr.a
  else if id = INFOBLOCK ∧ length.a = 2 ∧ a_1 = SETBID then
  "[ SETBID," + decode.blockop.a_2 + "]"
  else
   let code = a_1
   let recordtype = if id = MODULE then decode.moduleop.code
   else if id = TYPES then decode.typeop.code
   else if id = FUNCTIONBLK then decode.instop.code
   else if id = CONSTANTS then decode.constop.code else [ toword.code]
    if length.a = 1 then"[ toint." + recordtype + "]"
    else
     "[ toint." + recordtype + ","
     + @(seperator.",", toword,"", subseq(a, 2, length.a))
     + "]"

Function printrecord(id:blockop, a:seq.int)seq.word
 if id = VALUESYMTABLE then
 "function" + encodeword.tocharseq.subseq(a, 3, length.a) + "int" + toword.a_2
 else if a_1 = -1 then
 "[-1," + decode.blockop.a_2 + ","
  + @(seperator.",", toword,"", subseq(a, 2, length.a))
  + "]"
 else if a_1 = -2 then printabbr.a
 else if id = INFOBLOCK ∧ length.a = 2 ∧ a_1 = SETBID then
 "[ SETBID," + decode.blockop.a_2 + "]"
 else
  let code = a_1
  let recordtype = if id = MODULE then decode.moduleop.code
  else if id = TYPES then decode.typeop.code
  else if id = FUNCTIONBLK then decode.instop.code
  else if id = CONSTANTS then decode.constop.code else [ toword.code]
   if length.a = 1 then"[ toint." + recordtype + "]"
   else
    "[ toint." + recordtype + ","
    + @(seperator.",", toword,"", subseq(a, 2, length.a))
    + "]"