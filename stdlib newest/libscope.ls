Module libscope

use bits

use seq.int

use seq.liblib

use seq.libmod

use seq.libsym

use seq.mytype

use seq.seq.word


use seq.word

use stacktrace

use stdlib

use seq.encodingrep.seq.int


Function formatcall(modname:mytype, name:word, paratypes:seq.mytype)seq.word 
 print.modname +":"+ name + if length.paratypes = 0 
  then""
  else"("+ @(seperator.",", print,"", paratypes)+")"

Function formatcall(name:word, paratypes:seq.mytype)seq.word 
 [ name]+ if length.paratypes = 0 
  then""
  else"("+ @(seperator.",", print,"", paratypes)+")"

type libsym is record fsig:word, returntype:seq.word, instruction:seq.word

type liblib is record libname:seq.word, words:seq.encodingrep.seq.int, mods:seq.libmod, timestamp:int, readonly:boolean

Function liblib(a:seq.word, d:seq.libmod)liblib liblib(a, empty:seq.encodingrep.seq.int, d, 0, false)

Function timestamp(liblib)int export

Function libname(liblib)seq.word export

Function mods(liblib)seq.libmod export

Function words(liblib)seq.encodingrep.seq.int export


Function readonly(liblib)boolean export

Function =(a:libsym, b:libsym)boolean fsig.a = fsig.b

Function ?(a:libsym, b:libsym)ordering fsig.a ? fsig.b

function =(a:libmod, b:libmod)boolean modname.a = modname.b

Function =(t:mytype, b:mytype)boolean towords.t = towords.b

Function abstracttype(m:mytype)word towords(m)_length.towords.m

Function parameter(m:mytype)mytype mytype.subseq(towords.m, 1, length.towords.m - 1)

Function libsym(returntype:mytype, manglename:word, inst:seq.word)libsym 
 libsym(manglename, towords.returntype, inst)

Function returntype(libsym)seq.word export

Function instruction(libsym)seq.word export

Function fsig(libsym)word export

Function loadedlibs seq.liblib libs

function libs seq.liblib builtin.usemangle

type mytype is record towords:seq.word

Function mytype(seq.word)mytype export

Function towords(mytype)seq.word export

type libmod is record parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym

Function libmod(parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym)libmod 
 export

Function parameterized(libmod)boolean export

Function modname(libmod)word export

Function defines(libmod)seq.libsym export

Function exports(libmod)seq.libsym export

Function print(p:mytype)seq.word prt(towords.p, length.towords.p)

function prt(s:seq.word, i:int)seq.word 
 if i = 1 then [ s_1]else [ s_i]+"."+ prt(s, i - 1)

Function codedown(w:word)seq.seq.word 
 codedown(decode.w, 1, empty:seq.int,"", empty:seq.seq.word)

function codedown(l:seq.int, i:int, w:seq.int, words:seq.word, result:seq.seq.word)seq.seq.word 
 let charunderscore = 95 
  let charQ = 81 
  if i > length.l 
  then let a = if isempty.w then words else words + encodeword.w 
   if isempty.a then result else result + a 
  else if l_i = charminorseparator 
  then codedown(l, i + 1, empty:seq.int, words + encodeword.w, result)
  else if l_i = charmajorseparator 
  then codedown(l, i + 1, empty:seq.int, empty:seq.word, result +(words + encodeword.w))
  else if l_i = charQ 
  then assert i + 2 ≤ length.l report"format problem with codedown for"+ encodeword.l 
   let first = hexvalue(l_(i + 1))
   let t = first * 16 + hexvalue(l_(i + 2))
   if first > 0 
   then codedown(l, i + 3, w + t, words, result)
   else let t1 =((t * 16 + hexvalue(l_(i + 3)))* 16 + hexvalue(l_(i + 4)))* 16 + hexvalue(l_(i + 5))
   codedown(l, i + 6, w + t1, words, result)
  else codedown(l, i + 1, w + l_i, words, result)

function legal seq.int 
 decode("0123456789ABCDEFGHIJKLMNOPRSTUVWXYabcdefghijklmnopqrstuvwxy"_1)

function hexvalue(i:int)int if between(i, 48, 57)then i - 48 else i - 65 + 10

Function mangle(name:word, modname:mytype, parameters:seq.mytype)word 
 let nameandmodname = addword(empty:seq.int, name)+ codeup.modname 
  encodeword.@(+, codeup, nameandmodname, parameters)

function codeup(p:mytype)seq.int 
 // adds majorseparator before mytype // [ charmajorseparator]+ @(addword, identity, empty:seq.int, towords.p)

function addword(s:seq.int, w:word)seq.int 
 // adds minor separator between words // 
  @(codeup, identity, if isempty.s then s else s + charminorseparator, decode.w)

function charmajorseparator int // Z // 90

function charminorseparator int // z // 122

function codeup(l:seq.int, char:int)seq.int 
 // represent legal characters as themselves, and others as Qxx where xx is hexadecimal of byte or Q0xxxx // 
  let charQ = 81 
  if char in legal 
  then l + char 
  else if char < 256 
  then @(+, hexdigit.bits.char, l + charQ, [ 1, 0])
  else @(+, hexdigit.bits.char, l + charQ, [ 4, 3, 2, 1, 0])

function hexdigit(val:bits, digit:int)int legal_(toint(val >> 4 * digit ∧ bits.15)+ 1)


Function isabstract(a:mytype)boolean towords(a)_1 ="T"_1

Function isinstance(a:mytype)boolean length.towords.a > 1 ∧ not(parameter.a = mytype."T")

Function iscomplex(a:mytype)boolean length.towords.a > 1

Function replaceT(with:mytype, m:mytype)mytype 
 if towords(m)_1 ="T"_1 
  then mytype(towords.with + subseq(towords.m, 2, length.towords.m))
  else m

Function replaceT(with:mytype, name:word)word 
 if name = merge."empty:seq.T"
  then merge("empty:seq."+ print.with)
  else let d = decode.name 
  assert subseq(d, length.d, length.d)= [ 84]report"PROBLEM replacing T in word"+ name +"with"+ print.with 
  merge([ encodeword.subseq(d, 1, length.d - 1)]+ print.with)

Function emptyliblib(libname:word)liblib 
 let mymod = libmod(false, libname, empty:seq.libsym, empty:seq.libsym)
  liblib([ libname], [ mymod])

