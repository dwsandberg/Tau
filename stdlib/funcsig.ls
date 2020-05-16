#!/usr/local/bin/tau

run mylib testnew

module funcsig

use bits

use libscope

use packedseq.seq.mytype

use seq.seq.mytype

use seq.mytype

use seq.seq.sig

use seq.sig

use seq.encoding.fsignrep

use encoding.fsignrep

use seq.encodingrep.fsignrep

use intdict.fsignrep

use seq.fsignrep

use set.fsignrep

use stdlib

use otherseq.word

use seq.seq.word


type efsignrep is encoding fsignrep

Function efsignrep  erecord.fsignrep export

Function emptyprg prg prg.empty:intdict.fsignrep

Function decode(s:sig)fsignrep decode(efsignrep, toencoding.s)

Function ?(a:fsignrep, b:fsignrep)ordering fsig.a ? fsig.b ∧ module.a ? module.b

Function ?2(a:fsignrep, b:fsignrep)ordering fsig.a ? fsig.b

Function hash(a:fsignrep)int // hash(fsig.a + module.a) // hash.towords.a

Function =(a:fsignrep, b:fsignrep)boolean // fsig.a = fsig.b ∧ module.a = module.b // towords.a=towords.b


Function code(s:fsignrep)seq.sig export

Function returntype(s:fsignrep)seq.word export

Function towords(s:fsignrep)seq.word export

Function type:fsignrep internaltype export

type fsignrep is record fsig:seq.word, module:seq.word, upperbits:int, code:seq.sig, returntype:seq.word,
towords:seq.word

Function fsignrep(fsig:seq.word, module:seq.word, upperbits:int, code:seq.sig, returntype:seq.word,
towords:seq.word) fsignrep export

 function fsignrep(a:seq.word, b:seq.word, s:sig,ret:seq.word,towords:seq.word)fsignrep 
fsignrep(a, b, valueofencoding.s, empty:seq.sig,ret,towords )


Function nopara(s:fsignrep)int
 @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

Function nopara(s:sig)int
 let t = lownopara.s
  if t < 0 then
  let a = decode.s
    if module.a = "$"then toint.(fsig.a)_2 else nopara.a
  else t

Function fsig(fsignrep)seq.word export

Function module(fsignrep)seq.word export

function counttrue(i:int, b:boolean)int if b then i + 1 else i

type sig is record toencoding:encoding.fsignrep

Function type:sig internaltype export

Function type:prg internaltype export

Function valueofencoding(s:sig)int valueofencoding.toencoding.s

Function toencoding(sig)encoding.fsignrep export

Function sig(encoding.fsignrep)sig export

type prg is record translate:intdict.fsignrep


use deepcopy.sig

Function  sig (name:seq.word, args:seq.mytype, module:mytype, code:seq.sig)sig
 // will not set code when sig is already present // 
 sig (name , args , module , code ,mytype."")
 
Function  sig (name:seq.word, args:seq.mytype, module:mytype, code:seq.sig,returntype:mytype)sig
 // will not set code when sig is already present // 
 sig.encode(efsignrep, fsignrep3(name, args, module, code,returntype))


Function name(a:fsignrep)seq.word subseq(fsig.a, 1, findindex("("_1, fsig.a) - 1)

function parameters(a:fsignrep)seq.mytype
 let b = break(","_1, subseq(fsig.a, 1, length.fsig.a - 1), findindex("("_1, fsig.a) + 1)
  // assert false report @(seperator."\", identity,"", b)//
  @(+, mytype, empty:seq.mytype, b)

function break(w:word, a:seq.word, j:int)seq.seq.word
 let i = findindex(w, a, j)
  if i > length.a then
  if j > length.a then empty:seq.seq.word else [ subseq(a, j, i)]
  else [ subseq(a, j, i - 1)] + break(w, a, i + 1)

  use otherseq.mytype
  

function fsignrep3(name:seq.word, args:seq.mytype, module1:mytype, code:seq.sig,returntype:mytype)fsignrep
let module=towords.module1
 let upperbits = if length.module = 2 ∧ module_2 = "para"_1
 ∨ module_1 = "local"_1 then
 1 + localbit + nographbit + parabits.0
 else if last.module in "$words $int $word"then 1 + constbit + nographbit + parabits.0
 else if module_1 in "builtin"then 1 + nographbit + parabits.length.args
 else if module = "$constant"then 1 + parabits.0 + constbit
 else if module = "$fref"then 1 + parabits.0 + constbit
 else if module ="$" then
  if    name_1 in "BLOCK RECORD LOOPBLOCK APPLY" then
  1 + nographbit +lookcloserbit+ parabits.toint.name_2
 else  if name_1 in "CONTINUE" then
  1 + nographbit + parabits.toint.name_2
 else if   name_1 in "DEFINE" then
  1 + nographbit+lookcloserbit + parabits.1
  else  1 + parabits.length.args
 else if last.module="seq"_1 &and name="_" &and args=[mytype."T seq",mytype."int"] then
    1 + parabits.2 + lookcloserbit
 else
   let state=@(&or,hasstate,false,code)
   1 + parabits.length.args + 
   if state then statebit else if issimple(length.args , code)then inlinebit else 0
 let fsig = if length.args = 0 then name
 else
  name + "(" + @(seperator.",", towords,"", args)  + ")"
 let towords=if  module="local" then "LOCAL"+fsig
   else if  module="$int"  then "LIT"+fsig
   else if module="$words" then "WORDS"+toword.length.fsig+fsig
   else if module="$word" then "WORD"+fsig
   else if module in ["$"," $constant","$fref"] then fsig
   else [mangle(merge.name, module1, args),toword.length.args]
  fsignrep(fsig, module, upperbits, code,towords.returntype,towords)
  

Function lookuprep(p:prg, s:sig)fsignrep
 let a = lookup(translate.p, valueofencoding.s)
  if isempty.a then decode.s else a_1

Function add(p:prg, s:sig, code:seq.sig)prg
 let d = decode.s
 // assert not(  not.isinline.s &and issimple(nopara.d,code)) report "KK"+print.s //
  if code = code.d then p
  else prg.add(translate.p, valueofencoding.encode(efsignrep, d), 
  fsignrep(fsig.d, module.d, upperbits.d, code,returntype.d,towords.d))

Function =(a:sig, b:sig)boolean valueofencoding.a = valueofencoding.b

Function print(s:seq.sig)seq.word @(+, print,"", s)


function map(p:prg,d:encodingrep.fsignrep) fsignrep    
let a=lookup(translate.p,valueofencoding.code.d )
if isempty.a then data.d else a_1

Function getfsignrep(p:prg)  seq.fsignrep @(+,map.p, empty:seq.fsignrep,all.getinstance.efsignrep)


Function dumpprg(p:prg)seq.word @(seperator." &br", print.p,"", all.getinstance.efsignrep)

Function print(s:fsignrep)seq.word
 let t = module.s
  if t = "local"then [ merge("%" + fsig.s)]
  else if t = "$words"then '"' + fsig.s + '"'
  else if last.t in "$int $ "then
  if(fsig.s)_1 in "EXITBLOCK LOOPBLOCK CONTINUE BR"then fsig.s + " &br"else fsig.s
  else fsig.s + "[" + t + "]"

Function print(p:prg, e:encodingrep.fsignrep)seq.word
 let i = valueofencoding.code.e
 let bitflags =((([ toword.lowerbits.sig.code.e] + "(" + toword.lownopara.sig.code.e
 + ")"
 + if(bits.inlinebit ∧ bits.i) = bits.0 then""else"inline")
 + if(bits.constbit ∧ bits.i) = bits.0 then""else"c")
 + if(bits.localbit ∧ bits.i) = bits.0 then""else"l")
 + if(bits.nographbit ∧ bits.i) = bits.0 then""else"ng"
 let rep = lookuprep(p, sig.code.e)
  bitflags + print.rep + @(+, print,"", code.rep)

Function mangledname(s:fsignrep)word mangle(merge.name.s, mytype.module.s, parameters.s)

Function value(s:sig)int toint.(fsig.decode.s)_1

Function lit(i:int)sig
 let w = toword.i
  sig([ w], empty:seq.mytype, mytype."$int", empty:seq.sig)

Function block(i:int)sig
 sig([ "BLOCK"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig)


Function RECORD(i:int)sig
  sig([ "RECORD"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig)

Function loopblock(i:int)sig
  sig([ "LOOPBLOCK"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig)

Function apply(i:int)sig
  sig([ "APPLY"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig)

Function continue(i:int)sig
 sig([ "CONTINUE"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig)


Function define(w:word)sig
 let var = sig([ w], empty:seq.mytype, mytype."local", empty:seq.sig)
 sig([ "DEFINE"_1,w], empty:seq.mytype, mytype."$", [var])



function print(s:sig)seq.word print.decode.s

"Q2DZbuiltinZintZint Q2DZbuiltinZrealZreal Q2BZbuiltinZintZint Q2FZbuiltinZintZint Q2AZbuiltinZintZint Q3DZbuiltinZintZint Q3CQ3CZbuiltinZbitsZint Q3EQ3EZbuiltinZbitsZint"simplecalc list

function firstupperbit int 19

function paranobits int firstupperbit

Function nographbit int setupperbits(paranobits + 3, 0, 1)

function constbit int nographbit * 2

function localbit int constbit * 2

function inlinebit int localbit * 2

function lookcloserbit int inlinebit * 2

function statebit int  lookcloserbit * 2

Function lownopara(s:sig)int toint(bits.valueofencoding.s >> paranobits ∧ bits.7) - 1

Function isconst(s:sig)boolean(bits.constbit ∧ bits.valueofencoding.s) = bits.constbit

Function islocal(s:sig)boolean(bits.localbit ∧ bits.valueofencoding.s) = bits.localbit

Function isinline(s:sig)boolean(bits.inlinebit ∧ bits.valueofencoding.s) = bits.inlinebit

Function lookcloser(s:sig)boolean(bits.lookcloserbit ∧ bits.valueofencoding.s) = bits.lookcloserbit

Function hasstate(s:sig)boolean(bits.statebit ∧ bits.valueofencoding.s) = bits.statebit

Function isblock(s:sig)boolean check(s,"BLOCK")

Function isrecord(s:sig)boolean check(s,"RECORD")

Function isapply(s:sig)boolean check(s,"APPLY")

Function isloopblock(s:sig)boolean check(s,"LOOPBLOCK")

Function isdefine(s:sig)boolean  check(s,"DEFINE")


function check(s:sig, kind:seq.word)boolean
  if not.lookcloser.s then false else
 let t = decode(efsignrep, toencoding.s)
  module.t  = "$" ∧ subseq(fsig.t, 1, 1) = kind

Function parabits(nopara:int)int toint((bits.if nopara > 6 then 0 else nopara + 1) << paranobits)

function lastlocal int 8

Function exit sig ecvt(lastlocal + 1 + parabits.1 + nographbit)

Function br sig ecvt(lastlocal + 2 + parabits.3 + nographbit)

Function IDXUC sig ecvt(lastlocal + 3 + parabits.2 + nographbit+lookcloserbit)

Function CALLIDX sig ecvt(lastlocal + 4 + parabits.3 + nographbit)

Function STKRECORD sig ecvt(lastlocal + 5 + parabits.2 + nographbit)

Function skip sig ecvt(lastlocal + 6 + parabits.1)

Function lit0 sig ecvt(lastlocal + 7 + parabits.0 + nographbit +constbit )

Function wordEncodingOp sig ecvt(lastlocal + 8 +parabits.0 +lookcloserbit)

Function emptyseqOp sig     ecvt(lastlocal + 9 +parabits.0 + constbit )

Function mergeOp sig ecvt(lastlocal + 10 +parabits.1 +lookcloserbit)

Function makerealOp sig ecvt(lastlocal +11  +parabits.1+lookcloserbit)


Function plusOp sig      ecvt(lastlocal + 16 + nographbit + parabits.2 +lookcloserbit)

function +(s:sig, i:int)sig ecvt(valueofencoding.s + i)

Function eqOp sig plusOp + 4

Function gtOp sig plusOp + 5 

Function decodewordOp sig plusOp + 10



Function ecvt(i:int)sig builtin."LOCAL 1"

Function local1 sig ecvt(localbit + nographbit + 1 + parabits.0)

Function basesigs int
let discard = @(+, encode.efsignrep, empty:seq.encoding.fsignrep, startsigs)
 0

IDXUCZbuiltinZintZint

function startsigs seq.fsignrep [ 
fsignrep("1","local", local1,"?","LOCAL 1")
, fsignrep("2","local", local1 + 1,"?","LOCAL 2")
, fsignrep("3","local", local1 + 2,"?","LOCAL 3")
, fsignrep("4","local", local1 + 3,"?","LOCAL 4")
, fsignrep("5","local", local1 + 4,"?","LOCAL 5")
, fsignrep("6","local", local1 + 5,"?","LOCAL 6")
, fsignrep("7","local", local1 + 6,"?","LOCAL 7")
, fsignrep("8","local", local1 + 7,"?","LOCAL 8")
, fsignrep("EXITBLOCK 1","$", exit,"?","EXITBLOCK 1")
, fsignrep("BR 3","$", br,"?","BR 3")
, fsignrep("IDXUC 2","$", IDXUC,"?","IDXUC 2")
, fsignrep("callidx(int,T seq,int)","builtin", CALLIDX,"?","callidxZbuiltinZintZTzseqZint 3")
, fsignrep("STKRECORD(int,int)","builtin", STKRECORD,"?","STKRECORDZbuiltinZintZint 2")
, fsignrep("SET 0","$", skip,"?","SET 0")
, fsignrep("0","$int", lit0,"?","LIT 0")
, fsignrep("wordencoding","words", wordEncodingOp,"word encoding","wordencodingZwords 0")
, fsignrep("CONSTANT" + toword.lowerbits.lit0 + toword.lowerbits.lit0,"$constant", 
valueofencoding.emptyseqOp, [ lit0, lit0],"?","CONSTANT 15 15")
, fsignrep("merge(word seq)","words", mergeOp,"word","mergeZwordsZwordzseq 1")
, fsignrep("makereal(word seq)", "UTF8",makerealOp,"real","makerealZUTF8Zwordzseq 1")
,fsignrep("add( T erecord ,  T encodingrep )","builtin",ecvt(lastlocal +12 +parabits.2+statebit),"?","addZbuiltinZTzerecordZTzencodingrep 2")
,fsignrep("getinstance(T erecord)","builtin",ecvt(lastlocal +13 +parabits.1+statebit),"?","getinstanceZbuiltinZTzerecord 1")
,fsignrep(" getfile(bits seq ) ","builtin",ecvt(lastlocal +14 +parabits.1+statebit),"?","getfileZbuiltinZbitszseq 1")
,fsignrep("setfld2(T seq, int, T) ","builtin",ecvt(lastlocal +15 +parabits.3+statebit),"?","setfld2ZbuiltinZTzseqZintZT 3")
, fsignrep("+(int, int)","builtin", plusOp,"int","Q2BZbuiltinZintZint 2")
, fsignrep("-(int, int)","builtin", plusOp + 1 ,"int","Q2DZbuiltinZintZint 2")
, fsignrep("*(int, int)","builtin", plusOp + 2 ,"int"," Q2AZbuiltinZintZint 2")
, fsignrep("/(int, int)","builtin", plusOp + 3 ,"int","Q2FZbuiltinZintZint 2")
, fsignrep("=(int, int)","builtin", eqOp,"int","Q3DZbuiltinZintZint 2")
, fsignrep(">(int, int)","builtin", gtOp,"int","Q3EZbuiltinZintZint 2")
, fsignrep("<<(bits, int)","builtin", plusOp + 6 ,"bits","Q3CQ3CZbuiltinZbitsZint 2")
, fsignrep(">>(bits, int)","builtin", plusOp + 7 ,"bits","Q3EQ3EZbuiltinZbitsZint 2")
, fsignrep("-(real, real)","builtin", plusOp + 8 ,"real","Q2DZbuiltinZrealZreal 2")
  ,fsignrep("+(T seq, T seq)","word seq", plusOp + 9 ,"wordseq","Q2BZwordzseqZTzseqZTzseq 2")
, fsignrep("decode(T erecord, T encoding)","char seq encoding", plusOp + 10,"char seq","decodeZcharzseqzencodingZTzerecordZTzencoding 2")
]

function startsiglength int 34


Function assignencoding(l:int, s:fsignrep)int if l ≥ startsiglength then l + upperbits.s else upperbits.s

Function issimple(s:fsignrep)boolean issimple(nopara.s, code.s)

function issimple(nopara:int, code:seq.sig)boolean
  if between(length.code, 1, 15) ∧ between(nopara, 0, lastlocal)
 ∧ (nopara = 0 ∨ checksimple(code, 1, nopara, 0))
 then
   if nopara > 0 then true
   else 
   if      length.code=1 &and isconst.code_1 then
     let rep= decode.code_1
     if module.rep="$constant" &and length.code.rep= 3 then
         let arg1=  decode.(code.rep)_1
         let arg2=  decode.(code.rep)_2
         let arg3=  decode.(code.rep)_3
         let t=  not(module.arg1="$fref" &and module.arg2="$int" &and module.arg3="$word")
       //  assert t &or (fsig.arg3)_1 in "wordencodingwords mydatatestencoding
         mydata2testencoding mydata3testencoding mydata4testencoding ewordtest2" report "INTLINE" +print.code.rep+
          toword.(module.arg1="$fref")+toword(module.arg2="$int")+toword.(module.arg3="$word")
         +toword.t // t
     else 
         assert length.code &ne 4 &or not.isrecord.code_4 report "JKL"+print.code
  true 
  else true
else false

function toword(a:boolean) seq.word if a then "T" else "F"

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


function =(a:bits, b:bits)boolean toint.a = toint.b

Function lowerbits(s:sig)int valueofencoding.s - toint(bits.valueofencoding.s >> firstupperbit << firstupperbit)

Function lowerbits(s:int)int s - toint(bits.s >> firstupperbit << firstupperbit)

function lowerbits2(s:sig) sig ecvt.lowerbits.s

Function lowerbits(a:fsignrep) fsignrep
fsignrep( fsig.a, module.a, upperbits.a, @(+,lowerbits2,empty:seq.sig,code.a),  returntype.a,towords.a)


