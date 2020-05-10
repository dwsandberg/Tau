#!/usr/local/bin/tau

run pass2new test

module funcsig

use bits

use libscope

use packedseq.seq.mytype

use seq.seq.mytype

use seq.mytype

use seq.seq.sig

use seq.sig

use seq.encoding.sigrep

use encoding.sigrep

use seq.encodingrep.sigrep

use intdict.sigrep

use seq.sigrep

use set.sigrep

use stdlib

use otherseq.word

use seq.seq.word

/use sss

type esigrep is encoding sigrep

Function emptyprg prg prg.empty:intdict.sigrep

Function decode(s:sig)sigrep decode(esigrep, toencoding.s)

Function ?(a:sigrep, b:sigrep)ordering fsig.a ? fsig.b ∧ module.a ? module.b

Function ?2(a:sigrep, b:sigrep)ordering fsig.a ? fsig.b

Function code(s:sigrep)seq.sig export

Function type:sigrep internaltype export

type sigrep is record fsig:seq.word, module:seq.word, upperbits:int, code:seq.sig

Function nopara(s:sigrep)int
 @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

Function nopara(s:sig)int
 let t = lownopara.s
  if t < 0 then
  let a = decode.s
    if module.a = "$"then toint.(fsig.a)_2 else nopara.a
  else t

Function fsig(sigrep)seq.word export

Function module(sigrep)seq.word export

function counttrue(i:int, b:boolean)int if b then i + 1 else i

type sig is record toencoding:encoding.sigrep

Function type:sig internaltype export

Function type:prg internaltype export

Function valueofencoding(s:sig)int valueofencoding.toencoding.s

Function toencoding(sig)encoding.sigrep export

Function sig(encoding.sigrep)sig export

type prg is record translate:intdict.sigrep


use deepcopy.sig

Function sigrep(name:seq.word, args:seq.mytype, module:mytype, code:seq.sig)sig
 // will not set code when sig is already present // sig.encode(esigrep, sigrep3(name, args, towords.module, code))

Function name(a:sigrep)seq.word subseq(fsig.a, 1, findindex("("_1, fsig.a) - 1)

function parameters(a:sigrep)seq.mytype
 let b = break(","_1, subseq(fsig.a, 1, length.fsig.a - 1), findindex("("_1, fsig.a) + 1)
  // assert false report @(seperator."\", identity,"", b)//
  @(+, mytype, empty:seq.mytype, b)

function break(w:word, a:seq.word, j:int)seq.seq.word
 let i = findindex(w, a, j)
  if i > length.a then
  if j > length.a then empty:seq.seq.word else [ subseq(a, j, i)]
  else [ subseq(a, j, i - 1)] + break(w, a, i + 1)

function sigrep3(name:seq.word, args:seq.mytype, module:seq.word, code:seq.sig)sigrep
 let fname = @(+, towords, [ name], args)
 let upperbits = if length.module = 2 ∧ module_2 = "para"_1
 ∨ module_1 = "local"_1 then
 1 + localbit + nographbit + parabits.0
 else if last.module in "$words $int $word"then 1 + constbit + nographbit + parabits.0
 else if module_1 in "builtin"then 1 + nographbit + parabits.length.args
 else if module = "$constant"then 1 + parabits.0 + constbit
  else if module = "$fref"then 1 + parabits.0 + constbit
  else if module = "$define"then 1 + nographbit
  else
   1 + parabits.length.args + if issimple(length.fname - 1, code)then inlinebit else 0
 let fsig = if length.fname = 1 then fname_1
 else
  fname_1 + "(" + @(seperator.",", identity,"", subseq(fname, 2, length.fname))
  + ")"
  sigrep(fsig, module, upperbits, code)

Function lookuprep(p:prg, s:sig)sigrep
 let a = lookup(translate.p, valueofencoding.s)
  if isempty.a then decode.s else a_1

Function add(p:prg, s:sig, code:seq.sig)prg
 let sigrep = decode.s
  if code = code.sigrep then p
  else prg.add(translate.p, valueofencoding.encode(esigrep, sigrep), sigrep(fsig.sigrep, module.sigrep, upperbits.sigrep, code))

Function =(a:sig, b:sig)boolean valueofencoding.a = valueofencoding.b

Function print(s:seq.sig)seq.word @(+, print,"", s)

Function allsigreps seq.encodingrep.sigrep all.getinstance.esigrep

Function dumpprg(p:prg)seq.word @(seperator." &br", print.p,"", all.getinstance.esigrep)

Function print(s:sigrep)seq.word
 let t = module.s
  if t = "local"then [ merge("%" + fsig.s)]
  else if t = "$words"then '"' + fsig.s + '"'
  else if last.t in "$int $ $define"then
  if(fsig.s)_1 in "EXITBLOCK LOOPBLOCK CONTINUE BR"then fsig.s + " &br"else fsig.s
  else fsig.s + "[" + t + "]"

Function print(p:prg, e:encodingrep.sigrep)seq.word
 let i = valueofencoding.code.e
 let bitflags =((([ toword.lowerbits.sig.code.e] + "(" + toword.lownopara.sig.code.e
 + ")"
 + if(bits.inlinebit ∧ bits.i) = bits.0 then""else"inline")
 + if(bits.constbit ∧ bits.i) = bits.0 then""else"c")
 + if(bits.localbit ∧ bits.i) = bits.0 then""else"l")
 + if(bits.nographbit ∧ bits.i) = bits.0 then""else"ng"
 let rep = lookuprep(p, sig.code.e)
  bitflags + print.rep + @(+, print,"", code.rep)

Function mangledname(s:sigrep)word mangle(merge.name.s, mytype.module.s, parameters.s)

Function value(s:sig)int toint.(fsig.decode.s)_1

Function lit(i:int)sig
 let w = toword.i
  sigrep([ w], empty:seq.mytype, mytype."$int", empty:seq.sig)

Function block(i:int)sig
 let w = toword.i
  sig
  .encode(esigrep, sigrep(["BLOCK"_1, w],"$", 1 + nographbit + parabits.i, empty:seq.sig))

Function RECORD(i:int)sig
 let w = toword.i
  sig
  .encode(esigrep, sigrep(["RECORD"_1, w],"$", 1 + nographbit + parabits.i, empty:seq.sig))

Function loopblock(i:int)sig
 let w = toword.i
  sig
  .encode(esigrep, sigrep(["LOOPBLOCK"_1, w],"$", 1 + nographbit + parabits.i, empty:seq.sig))

Function apply(i:int)sig
 let w = toword.i
  sig
  .encode(esigrep, sigrep(["APPLY"_1, w],"$", 1 + nographbit + parabits.i, empty:seq.sig))

Function continue(i:int)sig
 let w = toword.i
  sig
  .encode(esigrep, sigrep(["CONTINUE"_1, w],"$", 1 + nographbit + parabits.i, empty:seq.sig))

Function define(w:word)sig
 let var = sigrep([ w], empty:seq.mytype, mytype."local", empty:seq.sig)
  sigrep("define" + w, empty:seq.mytype, mytype."$define", [ var])

function print(s:sig)seq.word print.decode.s

"Q2DZbuiltinZintZint Q2DZbuiltinZrealZreal Q2BZbuiltinZintZint Q2FZbuiltinZintZint Q2AZbuiltinZintZint Q3DZbuiltinZintZint Q3CQ3CZbuiltinZbitsZint Q3EQ3EZbuiltinZbitsZint"simplecalc list

function firstupperbit int 19

function paranobits int firstupperbit

Function nographbit int setupperbits(paranobits + 3, 0, 1)

function constbit int nographbit * 2

function localbit int constbit * 2

function inlinebit int localbit * 2

Function lownopara(s:sig)int toint(bits.valueofencoding.s >> paranobits ∧ bits.7) - 1

Function isconst(s:sig)boolean(bits.constbit ∧ bits.valueofencoding.s) = bits.constbit

Function islocal(s:sig)boolean(bits.localbit ∧ bits.valueofencoding.s) = bits.localbit

Function isinline(s:sig)boolean(bits.inlinebit ∧ bits.valueofencoding.s) = bits.inlinebit

Function isblock(s:sig)boolean check(s,"BLOCK")

Function isrecord(s:sig)boolean check(s,"RECORD")

Function isapply(s:sig)boolean check(s,"APPLY")

Function isloopblock(s:sig)boolean check(s,"LOOPBLOCK")

Function isdefine(s:sig)boolean module.decode(esigrep, toencoding.s) = "$define"

function check(s:sig, kind:seq.word)boolean
 let t = decode(esigrep, toencoding.s)
  module.t = "$" ∧ subseq(fsig.t, 1, 1) = kind

Function parabits(nopara:int)int toint((bits.if nopara > 6 then 0 else nopara + 1) << paranobits)

function lastlocal int 8

Function exit sig ecvt(lastlocal + 1 + parabits.1 + nographbit)

Function br sig ecvt(lastlocal + 2 + parabits.3 + nographbit)

Function IDXUC sig ecvt(lastlocal + 3 + parabits.2 + nographbit)

Function CALLIDX sig ecvt(lastlocal + 4 + parabits.3 + nographbit)

Function STKRECORD sig ecvt(lastlocal + 5 + parabits.2 + nographbit)

Function skip sig ecvt(lastlocal + 6 + parabits.1)

function startblock sig ecvt(lastlocal + 6)

Function plusOp sig ecvt(nographbit + parabits.2 + valueofencoding.startblock + 1)

function +(s:sig, i:int)sig ecvt(valueofencoding.s + i)

Function minusOp sig plusOp + 1

Function multOp sig plusOp + 2

Function divOp sig plusOp + 3

Function eqOp sig plusOp + 4

Function gtOp sig plusOp + 5

Function shiftleftOp sig plusOp + 6

Function shiftrightOp sig plusOp + 7

Function RsubOp sig plusOp + 8

Function indexOp sig plusOp + 9

Function catOp sig plusOp + 10

Function decodewordOp sig plusOp + 11

Function mergeOp sig ecvt(parabits.1 + lowerbits.valueofencoding.decodewordOp + 1)

Function wordEncodingOp sig ecvt(parabits.0 + lowerbits.valueofencoding.decodewordOp + 2)

Function lit0 sig ecvt(constbit + nographbit + parabits.0 + lowerbits.valueofencoding.decodewordOp + 3)

Function emptyseqOp sig ecvt(parabits.0 + constbit + lowerbits.valueofencoding.decodewordOp + 4)

function ecvt(i:int)sig builtin."PARAM 1"

Function local1 sig ecvt(localbit + nographbit + 1 + parabits.0)

Function basesigs int
let discard = @(+, encode.esigrep, empty:seq.encoding.sigrep, startsigs)
 0

function startsigs seq.sigrep [ sigrep("1","local", local1), sigrep("2","local", local1 + 1), sigrep("3","local", local1 + 2), sigrep("4","local", local1 + 3), sigrep("5","local", local1 + 4), sigrep("6","local", local1 + 5), sigrep("7","local", local1 + 6), sigrep("8","local", local1 + 7), sigrep("EXITBLOCK 1","$", exit), sigrep("BR 3","$", br)
, sigrep("IDXUC","$", IDXUC), sigrep("CALLIDX 3","$", CALLIDX), sigrep("STKRECORD 2","$", STKRECORD), sigrep("SET 0","$", skip), sigrep("+(int, int)","builtin", plusOp), sigrep("-(int, int)","builtin", minusOp), sigrep("*(int, int)","builtin", multOp), sigrep("/(int, int)","builtin", divOp), sigrep("=(int, int)","builtin", eqOp), sigrep(">(int, int)","builtin", gtOp)
, sigrep("<<(bits, int)","builtin", shiftleftOp), sigrep(">>(bits, int)","builtin", shiftrightOp), sigrep("-(real, real)","builtin", RsubOp), sigrep("_(T seq, int)","word seq", indexOp), sigrep("+(T seq, T seq)","word seq", catOp), sigrep("decode(T erecord, T encoding)","char seq encoding", decodewordOp), sigrep("merge(word seq)","words", mergeOp), sigrep("wordencoding","words", wordEncodingOp), sigrep("0","$int", lit0), sigrep("CONSTANT" + toword.lowerbits.lit0 + toword.lowerbits.lit0,"$constant", valueofencoding.emptyseqOp, [ lit0, lit0])]

function sigrep(a:seq.word, b:seq.word, s:sig)sigrep sigrep(a, b, valueofencoding.s, empty:seq.sig)

function sigrep(a:seq.word, b:seq.word, i:int)sigrep sigrep(a, b, i, empty:seq.sig)

Function assignencoding(l:int, s:sigrep)int if l ≥ length.startsigs then l + upperbits.s else upperbits.s

Function issimple(s:sigrep)boolean issimple(nopara.s, code.s)

function issimple(nopara:int, code:seq.sig)boolean
 between(length.code, 1, 15) ∧ between(nopara, 0, lastlocal)
 ∧ (nopara = 0 ∨ checksimple(code, 1, nopara, 0))

function checksimple(code:seq.sig, i:int, nopara:int, last:int)boolean
 // check that the parameters occur in order and they occur only once //
 // encodings of first three parameters is such that the encoding equals the parameter no. //
 if i > length.code then true
 else
  let low = lowerbits.code_i
   if low > nopara then checksimple(code, i + 1, nopara, last)
   else if low = last + 1 then checksimple(code, i + 1, nopara, last + 1)else false

function extractbit(no:int, i:int)int toint(bits.i >> no ∧ bits.1)

function setupperbits(no:int, i:int, val:int)int toint(bits.val << no ∨ bits.i)

Function hash(a:sigrep)int hash(fsig.a + module.a)

Function =(a:sigrep, b:sigrep)boolean fsig.a = fsig.b ∧ module.a = module.b

function =(a:bits, b:bits)boolean toint.a = toint.b

Function lowerbits(s:sig)int valueofencoding.s - toint(bits.valueofencoding.s >> firstupperbit << firstupperbit)

function lowerbits(s:int)int s - toint(bits.s >> firstupperbit << firstupperbit)