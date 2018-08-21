Module libscope

use bits

use seq.int

use seq.liblib

use seq.libmod

use seq.libsym

use seq.libtype

use seq.mytype

use seq.syminfo

use seq.word

use seq.seq.word

use stacktrace

use stdlib

Function print(l:libsym)seq.word 
 let i = syminfo.l 
  formatcall(modname.i, name.i, paratypes.i)+ print.returntype.i

Function formatcall(modname:mytype, name:word, paratypes:seq.mytype)seq.word 
 print.modname +":"+ name + if length.paratypes = 0 
  then""
  else"("+ @(seperator.",", print,"", paratypes)+")"

Function formatcall(name:word, paratypes:seq.mytype)seq.word 
 [ name]+ if length.paratypes = 0 
  then""
  else"("+ @(seperator.",", print,"", paratypes)+")"

type libsym is record fsig:word, returntype:seq.word, instruction:seq.word

type liblib is record libname:seq.word, types:seq.libtype, mods:seq.libmod, timestamp:int, readonly:boolean

Function liblib(a:seq.word, c:seq.libtype, d:seq.libmod)liblib liblib(a, c, d, 0, false)

Function liblib(a:seq.word, c:seq.libtype, d:seq.libmod, readonly:boolean)liblib liblib(a, c, d, 0, readonly)

Function timestamp(liblib)int export

Function libname(liblib)seq.word export

Function mods(liblib)seq.libmod export

Function types(liblib)seq.libtype export

Function readonly(liblib)boolean export

function =(a:libsym, b:libsym)boolean fsig.a = fsig.b

function =(a:libmod, b:libmod)boolean modname.a = modname.b ∧ library.a = library.b

Function =(t:mytype, b:mytype)boolean towords.t = towords.b

Function abstracttype(m:mytype)word towords(m)_length.towords.m

Function parameter(m:mytype)mytype mytype.subseq(towords.m, 1, length.towords.m - 1)

Function libsym(returntype:mytype, manglename:word, inst:seq.word)libsym 
 libsym(manglename, towords.returntype, inst)

Function returntypeold(s:libsym)mytype mytype.returntype.s

Function returntype(libsym)seq.word export


Function instruction(libsym)seq.word export

Function fsig(libsym)word export

Function libs seq.liblib builtin.usemangle

type libtype is record name:word, abstract:boolean, kind:word, subtypes:seq.mytype, size:offset, fldnames:seq.word

Function =(a:libtype, b:libtype)boolean name.a = name.b ∧ abstract.a = abstract.b

Function abstract(libtype)boolean export

Function name(libtype)word export

Function fortype(l:libtype)mytype 
 mytype.if abstract.l then"T"+ name.l else [ name.l]

Function subtypes(libtype)seq.mytype export

Function kind(libtype)word export

Function libtype(word, boolean, word, seq.mytype, offset, seq.word)libtype export

Function fldnames(libtype)seq.word export

Function size(libtype)offset export

type mytype is record towords:seq.word

Function mytype(seq.word)mytype export

Function towords(mytype)seq.word export

type libmod is record parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym, library:word

Function libmod(parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym, library:word)libmod 
 export

Function library(libmod)word export

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

type syminfo is record name:word, returntype:mytype, paratypes:seq.mytype, modname:mytype, instruction:seq.word, protoname:word, protoreturntype:mytype, protoparatypes:seq.mytype, mangled:word

Function syminfoX(mangled:word)syminfo 
 syminfo(mangled, mytype."", empty:seq.mytype, mytype."","", mangled, mytype."", empty:seq.mytype, mangled)

Function syminfoinstance(name:word, modname:mytype, paratypes:seq.mytype, returntype:mytype, instruction:seq.word, pname:word, pparatypes:seq.mytype, preturntype:mytype)syminfo 
 syminfo(name, returntype, paratypes, modname, instruction, pname, preturntype, pparatypes, mangle(pname, modname, pparatypes))

Function syminfo(name:word, modname:mytype, paratypes:seq.mytype, returntype:mytype, instruction:seq.word)syminfo 
 syminfo(name, returntype, paratypes, modname, instruction,"$noproto"_1, mytype."", empty:seq.mytype, mangle(name, modname, paratypes))

Function syminfo(name:word, paratypes:seq.mytype)syminfo 
 syminfo(name, mytype."X", paratypes, mytype."+","","$noproto"_1, mytype."", empty:seq.mytype,"?"_1)

Function =(a:syminfo, b:syminfo)boolean 
 encoding.name.a = encoding.name.b ∧ paratypes.a = paratypes.b ∧ modname.a = modname.b

Function hasproto(s:syminfo)boolean not(protoname.s ="$noproto"_1)

Function syminfo(s:libsym)syminfo 
 let c = codedown.fsig.s 
  let name = c_1_1 
  let modname = mytype(c_2)
  let parameters = @(+, mytype, empty:seq.mytype, subseq(c, 3, length.c))
  let src=
  // if length.instruction.s > 0 &and last.instruction.s="VERYSIMPLE"_1 then
    subseq(instruction.s,2 * length.parameters+1,length.instruction.s-1)
    else // instruction.s
  if isinstance.modname 
  then syminfo(if length.parameters = 0 then replaceT(parameter.modname, name)else name, replaceT(parameter.modname, returntypeold.s), 
  @(+, replaceT.parameter.modname, empty:seq.mytype, parameters), modname, src, name, returntypeold.s, parameters, fsig.s)
  else syminfo(name, returntypeold.s, parameters, modname, src,"$noproto"_1, mytype."", empty:seq.mytype, fsig.s)

Function changeinstruction(p:syminfo, inst:seq.word)syminfo 
 syminfo(name.p, returntype.p, paratypes.p, modname.p, inst, protoname.p, protoreturntype.p, protoparatypes.p, mangled.p)

Function tosyminfo(w:word)syminfo 
 let c = codedown.w 
  let name = c_1_1 
  let modname = mytype(c_2)
  let parameters = @(+, mytype, empty:seq.mytype, subseq(c, 3, length.c))
  if isinstance.modname 
  then syminfo(if length.parameters = 0 then replaceT(parameter.modname, name)else name, mytype."+", @(+, replaceT.parameter.modname, empty:seq.mytype, parameters), modname,"?", name, mytype."+", parameters, w)
  else syminfo(name, mytype."+", parameters, modname,"?","$noproto"_1, mytype."", empty:seq.mytype, w)

Function instruction(syminfo)seq.word export

Function name(syminfo)word export

Function returntype(syminfo)mytype export

Function paratypes(syminfo)seq.mytype export

Function modname(syminfo)mytype export

Function protoname(s:syminfo)word export

Function protoreturntype(s:syminfo)mytype export

Function protoparatypes(s:syminfo)seq.mytype export

Function protomodname(s:syminfo)mytype mytype.["T"_1, last.towords.modname.s]

Function mangled(syminfo)word export

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

Function libsymencoding erecord.libsym libsymencodingx

function hash(a:libsym)int encoding.fsig.a


use seq.libsym

type libsymencodingx is encoding libsym

function f42(mangledname:word, types:seq.mytype, l:libsym)seq.word 
 let info = syminfo.l 
  if mangledname = name.info ∧ types = paratypes.info + returntype.info 
  then [ fsig.l]
  else""

function f43(modname:word, mangledname:word, types:seq.mytype, l:libmod)seq.word 
 if modname = modname.l 
  then @(+, f42(mangledname, types),"", exports.l)
  else""

function f44(libname:word, modname:word, mangledname:word, types:seq.mytype, l:liblib)seq.word 
 if [ libname]= libname.l 
  then @(+, f43(modname, mangledname, types),"", mods.l)
  else""

Function findFunction(libname:word, modname:word, funcname:word, types:seq.mytype)seq.word 
 @(+, f44(libname, modname, funcname, types),"", libs)

Function emptyliblib(libname:word) liblib
let mymod = libmod(false, libname, empty:seq.libsym, empty:seq.libsym, libname)
  liblib([ libname], empty:seq.libtype, [ mymod])

______________________


type offset is record TSIZE:int, LIT:int

Function LIT(offset)int export

Function TSIZE(offset)int export


Function Tsize offset offset(1, 0)

Function offset(i:int)offset offset(0, i)

Function =(a:offset, b:offset)boolean TSIZE.a = TSIZE.b ∧ LIT.a = LIT.b

Function print(a:offset)seq.word 
 [ toword.LIT.a]+ if TSIZE.a = 0 then""else"TSIZE"+ toword.TSIZE.a

Function +(a:offset, b:offset)offset offset(TSIZE.a + TSIZE.b, LIT.a + LIT.b)

Function +(s:seq.int, b:offset)seq.int s + LIT.b

Function compose(a:offset, b:offset)offset offset(TSIZE.a * TSIZE.b, TSIZE.a * LIT.b + LIT.a)

