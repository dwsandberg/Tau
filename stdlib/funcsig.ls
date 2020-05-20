
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

  use otherseq.mytype



type efsignrep is encoding fsignrep

Function efsignrep  erecord.fsignrep export

Function emptyprg prg prg.empty:intdict.fsignrep

Function decode(s:sig)fsignrep decode(efsignrep, toencoding.s)

Function ?(a:fsignrep, b:fsignrep)ordering fsig.a ? fsig.b ∧ module.a ? module.b

Function ?2(a:fsignrep, b:fsignrep)ordering fsig.a ? fsig.b

Function hash(a:fsignrep)int  hash(fsig.a + module.a)   

Function =(a:fsignrep, b:fsignrep)boolean   fsig.a = fsig.b ∧ module.a = module.b  

Function code(s:fsignrep)seq.sig export

Function returntype(s:fsignrep)seq.word export

Function type:fsignrep internaltype export

Function fsig(fsignrep)seq.word export

Function module(fsignrep)seq.word export

type fsignrep is record fsig:seq.word, module:seq.word,  code:seq.sig, returntype:seq.word

Function nopara(s:fsignrep)int
 if module.s="$" then toint((fsig.s)_2)  else 
 @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

Function nopara(s:sig)int
 let t = lownopara.s
  if t < 0 then
  let a = decode.s
    if module.a = "$"then toint.(fsig.a)_2 else nopara.a
  else t

function counttrue(i:int, b:boolean)int if b then i + 1 else i

type sig is record toencoding:encoding.fsignrep

Function type:sig internaltype export

Function type:prg internaltype export

Function valueofencoding(s:sig)int valueofencoding.toencoding.s

Function toencoding(sig)encoding.fsignrep export

Function sig(encoding.fsignrep)sig export

type prg is record translate:intdict.fsignrep


/use deepcopy.sig

 
Function sig(name:seq.word, args:seq.mytype, module1:mytype, code:seq.sig,returntype:mytype)sig
 // will not set code when sig is already present // 
 let fsig = if length.args = 0 then name
 else
  name + "(" + @(seperator.",", towords,"", args)  + ")"
  sig(fsig,towords.module1,code,towords.returntype)
  

Function sig(fsig:seq.word,modname:seq.word,code:seq.sig,rettype:seq.word) sig
 sig(encode(efsignrep,fsignrep(fsig,modname,code,rettype)))


Function name(a:fsignrep)seq.word subseq(fsig.a, 1, findindex("("_1, fsig.a) - 1)

Function mangledname(a:fsignrep)word 
 let b = break(","_1, subseq(fsig.a, 1, length.fsig.a - 1), findindex("("_1, fsig.a) + 1)
let parameters= @(+, mytype, empty:seq.mytype, b)
mangle(merge.name.a, mytype.module.a, parameters)

function break(w:word, a:seq.word, j:int)seq.seq.word
 let i = findindex(w, a, j)
  if i > length.a then
  if j > length.a then empty:seq.seq.word else [ subseq(a, j, i)]
  else [ subseq(a, j, i - 1)] + break(w, a, i + 1)

Function assignencoding(l:int, s:fsignrep)int 
if l < length.baseupbits then 
  valueofencoding.baseupbits_(l+1)
else l+upperbits(s)
 
  
function upperbits(f:fsignrep) int
let module=module.f
let name=fsig.f
if length.module = 2 ∧ module_2 = "para"_1
 ∨ module_1 = "local"_1 then
 1 + parabits.0 + toint(localbit &or  nographbit )
 else if last.module in "$words $int $word"then 1 + parabits.0 + toint(constbit &or  nographbit )
  else if module = "$constant"then 1 + parabits.0 + toint.constbit
 else if module = "$fref"then 1 + parabits.0 + toint.constbit
 else if module ="$" then
  if    name_1 in "BLOCK RECORD LOOPBLOCK APPLY" then
  1 + parabits.toint.name_2+ toint(nographbit  &or lookcloserbit)
 else  if name_1 in "CONTINUE" then
  1  + parabits.toint.name_2 + toint.nographbit
 else if   name_1 in "DEFINE" then
  1 + parabits.1 + toint(nographbit &or lookcloserbit )
 else   1 + parabits.toint.name_2
 else if last.module="seq"_1 &and name="_(T seq,int)" then
    1 + parabits.2 + toint.lookcloserbit
 else let nopara=nopara.f 
  if module_1 in "builtin"then 1 + parabits.nopara + toint(nographbit  &or lookcloserbit)
 else
   let state=@(&or,hasstate,false,code.f)
   1 + parabits.nopara + 
   toint.if state then statebit else 
    // if between(length.code.f,2,14)  &and  isempty.@(+,filterinst,empty:seq.sig,code.f) then inlinebit
    else // if issimple(nopara , code.f)then inlinebit else bits.0
 

Function lookuprep(p:prg, s:sig)fsignrep
 let a = lookup(translate.p, valueofencoding.s)
  if isempty.a then decode.s else a_1

Function add(p:prg, s:sig, code:seq.sig)prg
 let d = decode.s
  // assert hasstate.s &or length.code > 14 &or isinline.s &or length.code=1 
   &or isempty.@(+,filterinst,empty:seq.sig,code)
  report "KK"+print.@(+,filterinst,empty:seq.sig,code) //
 // assert hasstate.s &or not(  not.isinline.s &and issimple(nopara.d,code)) report "KK"+print.[s] //
  let code2=if length.code.d =2 &and (code.d)_1=optionOp then [(code.d)_2]+code+optionOp else code
  if code2 = code.d then p
  else prg.add(translate.p, valueofencoding.encode(efsignrep, d), 
  fsignrep(fsig.d, module.d,  code2,returntype.d))
  
 / Function filterinst(s:sig) seq.sig  if lowerbits.valueofencoding.s &le startsiglength  &or isconst.s
  &or isblock.s  &or fsig.decode.s in ["<(T, T)","not(boolean)"]then empty:seq.sig else [s]
  
  hasstate.s &or length.code > 14 &or isinline.s &or length.code=1 
   not.state &and between(length.code,2,14)  &and  isempty.@(+,filterinst,empty:seq.sig,code)
  

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
 let bitflags =decodebits.i
 let rep = lookuprep(p, sig.code.e)
  bitflags + print.rep + @(+, print,"", code.rep)


Function value(s:sig)int toint.(fsig.decode.s)_1

Function lit(i:int)sig
 let w = toword.i
  sig([ w], empty:seq.mytype, mytype."$int", empty:seq.sig, mytype."?")

Function block(i:int)sig
 sig([ "BLOCK"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig, mytype."?")


Function RECORD(i:int)sig
  sig([ "RECORD"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig, mytype."?")

Function loopblock(i:int)sig
  sig([ "LOOPBLOCK"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig, mytype."?")

Function apply(i:int)sig
  sig([ "APPLY"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig, mytype."?")

Function continue(i:int)sig
 sig([ "CONTINUE"_1,toword.i], empty:seq.mytype, mytype."$", empty:seq.sig, mytype."?")


Function define(w:word)sig
 let var = sig([ w], empty:seq.mytype, mytype."local", empty:seq.sig, mytype."?")
 sig([ "DEFINE"_1,w], empty:seq.mytype, mytype."$", [var], mytype."?")

Function constant(args:seq.sig) sig
    let txt = @(+, toword,"", @(+, lowerbits, empty:seq.int, args))
     sig("CONSTANT" + txt, empty:seq.mytype, mytype."$constant", args, mytype."?")
     
Function wordsig(w:word) sig
sig([ w], empty:seq.mytype, mytype."$word", empty:seq.sig, mytype."word")

Function wordssig(w:seq.word) sig
   sig(w, empty:seq.mytype, mytype."$words", empty:seq.sig, mytype."word seq")
 


function print(s:sig)seq.word print.decode.s


function firstupperbit int 19

function paranobits int firstupperbit

Function nographbit bits   (bits.1 << paranobits + 3 )

function constbit bits nographbit << 1

function localbit bits nographbit << 2

function inlinebit bits nographbit << 3

function lookcloserbit bits nographbit << 4

function statebit   bits nographbit << 5

Function lownopara(s:sig)int toint(bits.valueofencoding.s >> paranobits ∧ bits.7) - 1

Function parabits(nopara:int)int toint((bits.if nopara > 6 then 0 else nopara + 1) << paranobits)


Function parabitsY(nopara:int)bits 
// added without check so will expanded in line //
 bits(nopara + 1) << paranobits 
 

Function isconst(s:sig)boolean( constbit ∧ bits.valueofencoding.s) =  constbit

Function islocal(s:sig)boolean( localbit ∧ bits.valueofencoding.s) =  localbit

Function isinline(s:sig)boolean( inlinebit ∧ bits.valueofencoding.s) = inlinebit

Function lookcloser(s:sig)boolean( lookcloserbit ∧ bits.valueofencoding.s) = lookcloserbit

Function hasstate(s:sig)boolean( statebit ∧ bits.valueofencoding.s) =  statebit

Function isblock(s:sig)boolean check(s,"BLOCK")

Function isrecord(s:sig)boolean check(s,"RECORD")

Function isapply(s:sig)boolean check(s,"APPLY")

Function isloopblock(s:sig)boolean check(s,"LOOPBLOCK")

Function isdefine(s:sig)boolean  check(s,"DEFINE")


function check(s:sig, kind:seq.word)boolean
  if not.lookcloser.s then false else
 let t = decode(efsignrep, toencoding.s)
  module.t  = "$" ∧ subseq(fsig.t, 1, 1) = kind


function lastlocal int 8


Function exit sig  baseupbits_(lastlocal+1)

Function br sig   baseupbits_(lastlocal+2)

Function IDXUC sig  baseupbits_(lastlocal+3)

Function CALLIDX sig baseupbits_(lastlocal+4)

Function STKRECORD sig baseupbits_(lastlocal+5)

Function skip sig baseupbits_(lastlocal+6)

Function lit0 sig baseupbits_(lastlocal+7)

Function wordEncodingOp sig baseupbits_(lastlocal+8)

Function emptyseqOp sig    baseupbits_(lastlocal+9)

Function optionOp sig baseupbits_(lastlocal+10)

Function plusOp sig     baseupbits_(lastlocal+16 ) 

Function eqOp sig   baseupbits_(lastlocal+17) 

Function gtOp sig   baseupbits_(lastlocal+18)




function ecvt(i:int)sig builtin."LOCAL 1"

function ecvt(i:bits)sig builtin."LOCAL 1"

use processOptions 

 
 function decodebits(i:int) seq.word
 ((([ toword.lowerbits.ecvt.i] + "(" + toword.lownopara.ecvt.i
 + ")"
 + if(inlinebit ∧ bits.i) = bits.0 then""else"inline")
 + if( constbit ∧ bits.i) = bits.0 then""else"c")
 + if( localbit ∧ bits.i) = bits.0 then""else"l")
 + (if( nographbit ∧ bits.i) = bits.0 then""else"ng")
 + (if( statebit ∧ bits.i) = bits.0 then""else"s")
 + if(lookcloserbit ∧ bits.i) = bits.0 then""else"lcr"
 
 Function decodebits(s:sig) seq.word
 let d=decode.s
 let i =valueofencoding.s
 { ", //"+fsig.d+"// ecvt(bits."+toword.lowerbits.s+"∨ parabitsY."+toword.lownopara.s
+ (if(inlinebit ∧ bits.i) = bits.0 then""else"∨ inlinebit")
 + (if( constbit ∧ bits.i) = bits.0 then""else"∨ constbit")
 + (if( localbit ∧ bits.i) = bits.0 then""else"∨ localbit")
 + (if( nographbit ∧ bits.i) = bits.0 then""else"∨ nographbit")
 + (if( statebit ∧ bits.i) = bits.0 then""else"∨ statebit")
 + if(lookcloserbit ∧ bits.i) = bits.0 then""else"∨ lookcloserbit" }
 +")"

 Function baseupbits seq.sig [
 // 1 // ecvt(bits.1 ∨ parabitsY.0 ∨ localbit ∨ nographbit) 
, // 2 // ecvt(bits.2 ∨ parabitsY.0 ∨ localbit ∨ nographbit) 
, // 3 // ecvt(bits.3 ∨ parabitsY.0 ∨ localbit ∨ nographbit) 
, // 4 // ecvt(bits.4 ∨ parabitsY.0 ∨ localbit ∨ nographbit) 
, // 5 // ecvt(bits.5 ∨ parabitsY.0 ∨ localbit ∨ nographbit) 
, // 6 // ecvt(bits.6 ∨ parabitsY.0 ∨ localbit ∨ nographbit) 
, // 7 // ecvt(bits.7 ∨ parabitsY.0 ∨ localbit ∨ nographbit) 
, // 8 // ecvt(bits.8 ∨ parabitsY.0 ∨ localbit ∨ nographbit) 
, // EXITBLOCK 1 // ecvt(bits.9 ∨ parabitsY.1 ∨ nographbit) 
, // BR 3 // ecvt(bits.10 ∨ parabitsY.3 ∨ nographbit) 
, // IDXUC(int, int)// ecvt(bits.11 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // callidx(int, T seq, int)// ecvt(bits.12 ∨ parabitsY.3 ∨ nographbit) 
, // STKRECORD(int, int)// ecvt(bits.13 ∨ parabitsY.2 ∨ nographbit) 
, // SET 1 // ecvt(bits.14 ∨ parabitsY.1) 
, // 0 // ecvt(bits.15 ∨ parabitsY.0 ∨ constbit ∨ nographbit) 
, // wordencoding // ecvt(bits.16 ∨ parabitsY.0 ∨ lookcloserbit) 
, // CONSTANT 15 15 // ecvt(bits.17 ∨ parabitsY.0 ∨ constbit) 
, // option(word seq, T)// ecvt(bits.18 ∨ parabitsY.2 ∨ nographbit) 
, // makereal(word seq)// ecvt(bits.19 ∨ parabitsY.1 ∨ lookcloserbit) 
, // add(T erecord, T encodingrep)// ecvt(bits.20 ∨ parabitsY.2 ∨ statebit) 
, // getinstance(T erecord)// ecvt(bits.21 ∨ parabitsY.1 ∨ statebit) 
, // getfile(bits seq)// ecvt(bits.22 ∨ parabitsY.1 ∨ statebit) 
, // setfld2(T seq, int, T)// ecvt(bits.23 ∨ parabitsY.3 ∨ statebit) 
, // +(int, int)// ecvt(bits.24 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // =(int, int)// ecvt(bits.25 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // >(int, int)// ecvt(bits.26 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // -(int, int)// ecvt(bits.27 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // *(int, int)// ecvt(bits.28 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // /(int, int)// ecvt(bits.29 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // ∨(bits, bits)// ecvt(bits.30 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // ∧(bits, bits)// ecvt(bits.31 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // <<(bits, int)// ecvt(bits.32 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // >>(bits, int)// ecvt(bits.33 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // -(real, real)// ecvt(bits.34 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // +(T seq, T seq)// ecvt(bits.35 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // decode(T erecord, T encoding)// ecvt(bits.36 ∨ parabitsY.2 ∨ nographbit ∨ lookcloserbit) 
, // merge(word seq)// ecvt(bits.37 ∨ parabitsY.1 ∨ lookcloserbit) ]


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



function =(a:bits, b:bits)boolean toint.a = toint.b

Function lowerbits(s:sig)int valueofencoding.s - toint(bits.valueofencoding.s >> firstupperbit << firstupperbit)

Function lowerbits(s:int)int s - toint(bits.s >> firstupperbit << firstupperbit)

function lowerbits2(s:sig) sig ecvt.lowerbits.s

module processOptions

use stdlib

use libscope

use seq.mytype

use funcsig

use seq.sig


function processOption(t:seq.word) seq.word
  if not(subseq(t,1,2)="* PROFILE") then ""
  else
   let modend=findindex(":"_1,t,3)
   let nameend=  findindex("("_1,t,modend+1)
   let paraend= findindex( ")"_1,t,nameend+1)
   let modname=(gettypelist.subseq(t,3,modend-1))_1
   let name= towords((gettypelist.subseq(t,modend+1,nameend-1))_1) _1
   let b=subseq(t,nameend+1,paraend-1)
   let args=if b="" then empty:seq.mytype else gettypelist.subseq(t,nameend+1,paraend-1)
   let ret=(gettypelist.subseq(t,paraend+1,length.t))_1
   let discard= [sig([name], args,modname,[optionOp,wordssig("PROFILE")], ret)]
   print.modname
   +"&br"+name
   +"&br"+@(seperator."+",print,"",args)
   +"&br"+print.ret

function gettypelist(s:seq.word) seq.mytype
      gettype(s,1,"",empty:seq.mytype)

function  gettype( s:seq.word,i:int,result:seq.word,l:seq.mytype) seq.mytype
if i > length.s then  l+mytype.result
else 
if s_i=","_1 then gettype(s,i+1,"",l+mytype.result ) 
else  
   let j=if  i < length.s &and s_(i+1)="."_1 then  i+2 else i+1 
  gettype(s,j,[s_i]+result,  l)
      
 
Function basesigs(allsrc:seq.seq.word) int
let b=[ 
sig("1","local", empty:seq.sig,"?")
, sig("2","local", empty:seq.sig,"?")
, sig("3","local", empty:seq.sig,"?")
, sig("4","local", empty:seq.sig,"?")
, sig("5","local", empty:seq.sig,"?")
, sig("6","local", empty:seq.sig,"?")
, sig("7","local", empty:seq.sig,"?")
, sig("8","local", empty:seq.sig,"?")
, sig("EXITBLOCK 1","$",empty:seq.sig,"?")
, sig("BR 3","$", empty:seq.sig,"?")
, sig("IDXUC(int,int)","builtin", empty:seq.sig,"?") 
, sig("callidx(int,T seq,int)","builtin", empty:seq.sig,"?")
, sig("STKRECORD(int,int)","builtin", empty:seq.sig,"?")
, sig("SET 1","$", empty:seq.sig,"?")
, sig("0","$int", empty:seq.sig,"?")
, sig("wordencoding","words", empty:seq.sig,"word encoding")
, sig(// "CONSTANT" + toword.lowerbits.lit0  + toword.lowerbits.lit0 //  "CONSTANT 15 15","$constant" 
, [ lit0, lit0],"?")  
, sig("option(word seq,T)","builtin",empty:seq.sig,"$")  
, sig("makereal(word seq)", "UTF8", empty:seq.sig,"real")
, sig("add( T erecord ,  T encodingrep )","builtin", empty:seq.sig,"?")
, sig("getinstance(T erecord)","builtin",empty:seq.sig,"?")
, sig(" getfile(bits seq ) ","builtin",empty:seq.sig,"?")
, sig("setfld2(T seq, int, T) ","builtin",empty:seq.sig,"?")
, sig("+(int, int)","builtin", empty:seq.sig,"int")
, sig("=(int, int)","builtin", empty:seq.sig,"int")
, sig(">(int, int)","builtin", empty:seq.sig,"int")
, sig("-(int, int)","builtin", empty:seq.sig,"int")
, sig("*(int, int)","builtin", empty:seq.sig,"int")
, sig("/(int, int)","builtin", empty:seq.sig,"int")
, sig("∨(bits, bits)","builtin", empty:seq.sig ,"bits")
, sig("∧(bits, bits)","builtin", empty:seq.sig,"bits")
, sig("<<(bits, int)","builtin", empty:seq.sig ,"bits")
, sig(">>(bits, int)","builtin", empty:seq.sig,"bits")
, sig("-(real, real)","builtin", empty:seq.sig,"real")
, sig("+(T seq, T seq)","word seq", empty:seq.sig,"wordseq")
, sig("decode(T erecord, T encoding)","char seq encoding", empty:seq.sig,"char seq")
, sig("merge(word seq)","words", empty:seq.sig,"word")
]
let discard2=@(+,processOption,"",allsrc) 
// assert false report @(seperator."&br",decodebits,"",b) //
assert length.b=length.baseupbits report "basesig problem"
 0

