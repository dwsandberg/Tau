
run mylib testnew

module funcsig

use bits

use libscope

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

use mangle

use mytype


type efsignrep is encoding fsignrep

Function efsignrep  erecord.fsignrep export

Function emptyprg prg prg.empty:intdict.target

Function keys(p:prg) seq.int  keys.translate.p

Function data(p:prg) seq.target data.translate.p

Function decode(s:sig)fsignrep decode(efsignrep, toencoding.s)

Function hash(a:fsignrep)int  hash(fsig.a + module.a)   

Function =(a:fsignrep, b:fsignrep)boolean   fsig.a = fsig.b ∧ module.a = module.b  

Function cleancode(s:fsignrep)seq.sig code.s

Function returntype(s:fsignrep)seq.word export

Function type:fsignrep internaltype export

Function fsig(fsignrep)seq.word export

Function module(fsignrep)seq.word export

type fsignrep is record fsig:seq.word, module:seq.word,  code:seq.sig, returntype:seq.word,extrabits:bits


 

Function noparafsignrep(s:fsignrep)int
 if module.s="$" then toint((fsig.s)_2)  else 
 @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

Function nopara(s:sig)int
 let t = lownopara.s
  if t < 0 then
  let a = decode.s
    if module.a = "$"then toint.(fsig.a)_2 else noparafsignrep.a
  else t

function counttrue(i:int, b:boolean)int if b then i + 1 else i

type sig is record toencoding:encoding.fsignrep

Function type:sig internaltype export

Function type:prg internaltype export

Function valueofencoding(s:sig)int valueofencoding.toencoding.s

Function toencoding(sig)encoding.fsignrep export

Function sig(encoding.fsignrep)sig export

type prg is record translate:intdict.target

type target is record target:sig,code:seq.sig

Function target(target) sig export

Function code(target) seq.sig export

Function constantcode(s:fsignrep) seq.sig
 if module.s in ["$fref" ,"$constant"] then
   let a= @(+,ecvt,empty:seq.sig, @(+,toint,empty:seq.int,subseq(fsig.s,2,length.fsig.s)))  
  // assert a=code.s &or emptyseqOp=sig.s report "HHH"+fsig.s //
   code.s
 else empty:seq.sig

Function target(sig,seq.sig) target export

Function type:target internaltype export

use intdict.target

Function FREFsig(s:sig) sig  
sig55("FREF" + toword.valueofencoding.s, "$fref", [ s],"?")  

/function fsignrep(name:seq.word, args:seq.mytype, module1:mytype, code:seq.sig,returntype:mytype)fsignrep
 // will not set code when sig is already present // 
   fsignrep(tofsig(name,args),towords.module1,code,towords.returntype,bits.0)


Function fsignrep(name:seq.word, args:seq.mytype, module1:mytype, returntype:mytype)fsignrep
 // will not set code when sig is already present // 
   fsignrep(tofsig(name,args),towords.module1,empty:seq.sig,towords.returntype,bits.0)

Function sig(fsig:seq.word,modname:seq.word,rettype:seq.word,b:bits) sig
  sigOK.fsignrep(fsig,modname,empty:seq.sig,rettype,b)


Function sig(fsig:seq.word,module:seq.word,returntype:seq.word) sig
      sig(fsig,module,returntype,bits.0)

Function sig(name:seq.word, args:seq.mytype, module1:mytype, returntype:mytype)sig
 // will not set code when sig is already present // 
   sig(tofsig(name,args),towords.module1,towords.returntype)
   


Function sig58(name:seq.word, args:seq.mytype, module1:mytype, code:seq.sig,returntype:mytype)sig
 // will not set code when sig is already present // 
   sig(encode(efsignrep,fsignrep(tofsig(name,args),towords.module1,code,towords.returntype,bits.0)))
   
function sigOK(f:fsignrep) sig sig(encode(efsignrep,f))




Function sig55(fsig:seq.word,modname:seq.word,code:seq.sig,rettype:seq.word) sig
 sig(encode(efsignrep,fsignrep(fsig,modname,code,rettype,bits.0)))

 

  
  function tofsig(name:seq.word, args:seq.mytype) seq.word
   if length.args = 0 then name else  name + "(" + @(seperator.",", towords,"", args)  + ")"
   
 
  

use stacktrace
 
  

Function findencode(f:fsignrep) seq.fsignrep   findencode(efsignrep,f)

Function findencode(s:symbol) seq.fsignrep   
findencode(efsignrep,fsignrep(fsig.s,module.s,empty:seq.sig,returntype.s,bits.0))


Function name(a:fsignrep)seq.word 
let j=findindex("("_1, fsig.a)  
if j > length.fsig.a then fsig.a
 else
subseq(fsig.a, 1, j - 1)


Function mangledname(s:fsignrep)word 
mangle2( name.s ,  module.s, @(+,towords,empty:seq.seq.word,paratypes.s))


Function paratypes(f:fsignrep) seq.mytype
let a= fsig.f 
  if length.a < 4 then empty:seq.mytype
  else 
  let i=if a_(length.a-1)="*"_1 then 2 else 1
 let b = break(","_1, subseq(a, 1, length.a - i), findindex("("_1, a) + 1 )
 @(+, mytype, empty:seq.mytype, b)


function break(w:word, a:seq.word, j:int)seq.seq.word
 let i = findindex(w, a, j)
  if i > length.a then
  if j > length.a then empty:seq.seq.word else [ subseq(a, j, i)]
  else [ subseq(a, j, i - 1)] + break(w, a, i + 1)

Function assignencoding(l:int, s:fsignrep)int 
if l < length.baseupbits then 
  valueofencoding.baseupbits_(l+1)
else 
l+1+toint(upperbits(s,l) &or extrabits.s)
 
  
function upperbits(f:fsignrep,l:int) bits
let module=module.f
let name=fsig.f
if length.module = 2 ∧ module_2 = "para"_1
 ∨ module_1 = "local"_1 then
  parabits.0  &or(localbit )
 else if last.module in "$words $int $word"then 
 parabits.0  &or (constbit  )
  else if module = "$constant"then 
  parabits.0  &or constbit
 else if module = "$fref"then 
  parabits.0  &or  constbit
 else if module ="$" then
  if    name_1 in "BLOCK RECORD LOOPBLOCK APPLY CONTINUE" then
   parabits.toint.name_2 &or  lookcloserbit 
 else if   name_1 in "DEFINE" then
   parabits.1  &or  lookcloserbit 
 else   
  parabits.toint.name_2
 else let nopara=noparafsignrep.f 
 if  nopara=2 &and last.module="seq"_1 &and  (name="_(T seq,int)" &or name=
           "_("+subseq(module,1,length.module-1)+"seq,int)")
  then
     parabits.2  &or lookcloserbit
 else 
  if module_1 in "builtin"then 
   parabits.nopara  &or ( lookcloserbit)
 else
   if length.code.f=0  then if
     l > // size of basesigs  // 43 then  parabits.nopara  &or (statebit ) else parabits.nopara
   else
    let options= if  not(last.code.f=optionOp) then "" else fsig.decode.(code.f)_(length.code.f-1)  
   let state=@(&or,hasstate,"STATE"_1 in options,code.f)
    parabits.nopara  &or 
      (if state then statebit else     bits.0  )
     &or if    "INLINE"_1 in options  then inlinebit
         else  if   "NOINLINE"_1 in options &or (length.code.f=3 &and length.options > 0   ) then bits.0
         else  if  length.code.f < 15 &or issimple(nopara , code.f) then inlinebit
         else bits.0
     
Function lookuprep(p:prg, s:sig)fsignrep
 let f=decode.s
 let a = lookup(translate.p, valueofencoding.s)
  if isempty.a then 
     f else  fsignrep(fsig.f,module.f,code.a_1,returntype.f,bits.0) 

Function lookupcode (p:prg, s:sig) seq.target
  lookup(translate.p, valueofencoding.s)
 
 Function map(p:prg,s:sig,code:seq.sig) prg
   prg(add(translate.p,valueofencoding.s,target(s,code)))
   
 Function map(p:prg,s:sig,t:sig,code:seq.sig) prg
   prg(add(translate.p,valueofencoding.s,target(t,code)))


     use seq.target    

Function add(p:prg, s:sig, code:seq.sig)prg
 let d = decode.s
  let code2=
     if length.code.d =3 &and (code.d)_3=optionOp  then 
       if  subseq(code,length.code-1,length.code) = subseq(code.d,length.code.d-1,length.code.d) then code
       else 
      code+[(code.d)_2]+optionOp  
  else code
  prg.add(translate.p, valueofencoding.s, target(s, code2 ))
    

Function =(a:sig, b:sig)boolean valueofencoding.a = valueofencoding.b

Function print(s:seq.sig)seq.word @(+, print,"", s)


function map(p:prg,d:encodingrep.fsignrep) fsignrep    
let a=lookup(translate.p,valueofencoding.code.d )
if isempty.a then if  module.data.d in ["$constant" ,"$fref"] then data.d else
 // assert isempty.code.data.d &or module.data.d in ["$constant" ,"$fref","$"] 
       &or  parameter.mytype.module.data.d =mytype."T"
  report "PPP"+ print.data.d+fsig.data.d+module.data.d
  data.d //
  fsignrep(fsig.data.d,module.data.d,empty:seq.sig,returntype.data.d,bits.0)
else
fsignrep(fsig.data.d,module.data.d,code.a_1,returntype.data.d,bits.0)


Function getfsignrep(p:prg)  seq.fsignrep @(+,map.p, empty:seq.fsignrep,all.getinstance.efsignrep)


Function dumpprg(p:prg)seq.word @( +, print.p,"", all.getinstance.efsignrep)

Function print(s:fsignrep)seq.word
 let t = module.s
  if t = "local"then [ merge("%" + fsig.s)]
  else if t = "$words"then '"' + fsig.s + '"'
  else if t = "$constant" then   let tmp="CONSTANT{"+ print.code.s +"}" 
     if tmp="CONSTANT{ 0 0 } " then "emptyseq"  else tmp
  else if last.t in "$int $ "then
  if(fsig.s)_1 in "EXITBLOCK LOOPBLOCK CONTINUE BR"then fsig.s + " &br"else fsig.s
  else fsig.s + "[" + t + "]"

Function print(p:prg, e:encodingrep.fsignrep)seq.word
 let i = valueofencoding.code.e
 let bitflags =decodebits.i
 let rep = lookuprep(p, sig.code.e)
 " &br"+bitflags + print.rep   + @(+, print,"", code.rep)
   
  
Function print(p:prg, s:sig)seq.word
 if lowerbits.s &le length.baseupbits then "" else 
 let rep=lookuprep(p,s) 
  decodebits.s+ print.rep + @(+, print,"", code.rep)
   


Function value(s:sig)int toint.(fsig.decode.s)_1

Function lit(i:int)sig
 let w = toword.i
  sig([ w],  "$int", "int")

Function block(i:int)sig sig([ "BLOCK"_1,toword.i],  "$",   "?")

Function RECORD(i:int)sig sig([ "RECORD"_1,toword.i],    "$",  "?")

Function loopblock(i:int)sig sig([ "LOOPBLOCK"_1,toword.i],   "$",  "?")

Function apply(i:int)sig  sig([ "APPLY"_1,toword.i],   "$",   "?")

Function continue(i:int)sig  sig([ "CONTINUE"_1,toword.i],    "$",   "?")


Function define(w:word)sig
 let var = sig([ w], "local","?")
 sig55([ "DEFINE"_1,w],"$", [var],"?")

Function constant(args:seq.sig) sig
    let txt = @(+, toword,"",   @(+, lowerbits, empty:seq.int, args) )
     sig55("CONSTANT" + txt, "$constant", args, "?")
     
Function wordsig(w:word) sig sig([ w], "$word", "word")

Function wordssig(w:seq.word) sig sig(w,"$words",  "word seq")
 
  
Function local(i:int) sig   sig([ toword.i], "local", "?")

Function print(s:sig)seq.word print.decode.s

function firstupperbit int 19

function paranobits int firstupperbit

Function statebit bits   (bits.1 << paranobits + 3 )

function constbit bits statebit << 1

function localbit bits statebit << 2

function inlinebit bits statebit << 3

Function lookcloserbit bits statebit << 4




function lownopara(s:sig)int toint(bits.valueofencoding.s >> paranobits ∧ bits.7) - 1

Function parabits(nopara:int)bits (bits.if nopara > 6 then 0 else nopara + 1) << paranobits


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

Function local1 sig baseupbits_1

Function exit sig  baseupbits_(lastlocal+1)

Function br sig   baseupbits_(lastlocal+2)

Function IDXUC sig  baseupbits_(lastlocal+3)

Function CALLIDX sig baseupbits_(lastlocal+4)

Function STKRECORD sig baseupbits_(lastlocal+5)

Function notOp sig baseupbits_(lastlocal+6)

Function lit0 sig baseupbits_(lastlocal+7)

Function wordEncodingOp sig baseupbits_(lastlocal+8)

Function emptyseqOp sig    baseupbits_(lastlocal+9)

Function optionOp sig ecvt(bits.18 ∨ parabitsY.2  &or statebit) 

 
Function plusOp sig   ecvt(bits.19 ∨ parabitsY.2   ∨ lookcloserbit) 

Function eqOp  sig   ecvt(bits.20 ∨ parabitsY.2   ∨ lookcloserbit) 

Function gtOp sig   ecvt(bits.21 ∨ parabitsY.2  ∨ lookcloserbit)



Function ecvt(i:int)sig  sig.to:encoding.fsignrep(i)

function ecvt(i:bits)sig sig.to:encoding.fsignrep(toint.i)

use processOptions 

 
 function decodebits(i:int) seq.word
 ((([ toword.lowerbits.ecvt.i] + "(" + toword.lownopara.ecvt.i
 + ")"
 + if(inlinebit ∧ bits.i) = bits.0 then""else"inline")
 + if( constbit ∧ bits.i) = bits.0 then""else"c")
 + if( localbit ∧ bits.i) = bits.0 then""else"l")
 + (if( statebit ∧ bits.i) = bits.0 then""else"s")
 + if(lookcloserbit ∧ bits.i) = bits.0 then""else"lcr"
 
 Function decodebits(s:sig) seq.word
 let d=decode.s
 let i =valueofencoding.s
 { ", //"+fsig.d+"// ecvt(bits."+toword.lowerbits.s+"∨ parabitsY."+toword.lownopara.s
+ (if(inlinebit ∧ bits.i) = bits.0 then""else"∨ inlinebit")
 + (if( constbit ∧ bits.i) = bits.0 then""else"∨ constbit")
 + (if( localbit ∧ bits.i) = bits.0 then""else"∨ localbit")
 + (if( statebit ∧ bits.i) = bits.0 then""else"∨ statebit")
 + (if(lookcloserbit ∧ bits.i) = bits.0 then""else"∨ lookcloserbit" )
  }
 +")"

 Function baseupbits seq.sig 
 // statebit is set on option so that adding an option doesn't auto add a inline bit //
 [
 // 1 // ecvt(bits.1 ∨ parabitsY.0 ∨ localbit ) 
, // 2 // ecvt(bits.2 ∨ parabitsY.0 ∨ localbit ) 
, // 3 // ecvt(bits.3 ∨ parabitsY.0 ∨ localbit ) 
, // 4 // ecvt(bits.4 ∨ parabitsY.0 ∨ localbit ) 
, // 5 // ecvt(bits.5 ∨ parabitsY.0 ∨ localbit ) 
, // 6 // ecvt(bits.6 ∨ parabitsY.0 ∨ localbit ) 
, // 7 // ecvt(bits.7 ∨ parabitsY.0 ∨ localbit ) 
, // 8 // ecvt(bits.8 ∨ parabitsY.0 ∨ localbit ) 
, // EXITBLOCK 1 // ecvt(bits.9 ∨ parabitsY.1 ) 
, // BR 3 // ecvt(bits.10 ∨ parabitsY.3 ) 
, // IDXUC(int, int)// ecvt(bits.11 ∨ parabitsY.2  ∨ lookcloserbit) 
, // callidx(int, T seq, int)// ecvt(bits.12 ∨ parabitsY.3 ) 
, // STKRECORD(int, int)// ecvt(bits.13 ∨ parabitsY.2 ) 
, // not(boolean)   //      ecvt(bits.14 ∨ parabitsY.1   )
, // 0 // ecvt(bits.15 ∨ parabitsY.0 ∨ constbit ) 
, // wordencoding // ecvt(bits.16 ∨ parabitsY.0 ∨ lookcloserbit) 
, // CONSTANT 15 15 // ecvt(bits.17 ∨ parabitsY.0 ∨ constbit) 
, // option(word seq, T)// ecvt(bits.18 ∨ parabitsY.2  &or statebit) 
]

Function issimple(s:fsignrep)boolean issimple(noparafsignrep.s, code.s)

function issimple(nopara:int, code:seq.sig)boolean
    between(length.code, 1, 15) ∧ between(nopara, 0, lastlocal)
 ∧ (nopara = 0 ∨ checksimple(code, 1, nopara, 0))
 
function toword(a:boolean) seq.word if a then "T" else "F"

function checksimple(code:seq.sig, i:int, nopara:int, last:int)boolean
 // check that the parameters occur in order and they occur only once //
 // encodings of first 8 parameters is such that the encoding equals the parameter no. //
 // any op that may involve state must occur after all parameters //
 if i > length.code then true
 else
  if  nopara < last &and // should also check for loopblock // hasstate.code_i then 
   // state op between parameters //
   false
   else
  let low = lowerbits.code_i
   if low > nopara then checksimple(code, i + 1, nopara, last)
   else if low = last + 1 then checksimple(code, i + 1, nopara, last + 1)else false

function extractbit(no:int, i:int)int toint(bits.i >> no ∧ bits.1)

function =(a:bits, b:bits)boolean toint.a = toint.b

Function lowerbits(s:sig)int valueofencoding.s - toint(bits.valueofencoding.s >> firstupperbit << firstupperbit)

Function lowerbits(s:int)int s - toint(bits.s >> firstupperbit << firstupperbit)

Function isinOp(s:sig) boolean
   lookcloser.s &and (fsig.decode.s)_1 in "in ="
   
Function tosymbol(s:sig) symbol
   let f=decode.s
   if module.f="$fref" then
     let arg=tosymbol((constantcode.f)_1)
     let t= symbol("FREF"+fsig.arg+module.arg,"$fref","?",[arg])
     t
   else 
   symbol(fsig.f,module.f,returntype.f, empty:seq.symbol)
   
   Function tosig( s:symbol) sig  
          if module.s="$fref" then FREFsig.tosig.(zcode.s)_1 else 
          if module.s="$" &and  (fsig.s)_1="DEFINE"_1 then     define.(fsig.s)_2
       else   if last.module.s = "para"_1 then  sig([ (module.s)_1], "local", "?") 
        else 
           sig (fsig.s ,  module.s,returntype.s)

use seq.symbol

module processOptions

use stdlib

use funcsig

use seq.sig


use seq.seq.word

use bits


function processOption(t:seq.word) seq.word
  if length.t < 4 &or not(t_1="*"_1) &or  not (t_2 in "PROFILE INLINE") then ""
   else
   let code=[lit.1,wordssig([t_2]),optionOp]
   let modend=findindex(":"_1,t,3)
   let nameend=  findindex("("_1,t,modend+1)
   let paraend= findindex( ")"_1,t,nameend+1)
   let modname=(gettypelist.subseq(t,3,modend-1))_1
   let name= ((gettypelist.subseq(t,modend+1,nameend-1))_1) _1
   let b=subseq(t,nameend+1,paraend-1)
   let args=if b="" then empty:seq.seq.word else gettypelist.subseq(t,nameend+1,paraend-1)
   let ret=(gettypelist.subseq(t,paraend+1,length.t))_1
  let discard= [sig55([name]+"("+@(seperator.",",identity,"",args)+")",modname,code, ret)]
   "&br"+printastype.modname+":"+name+"("+@(seperator.",",printastype,"",args)+")"
  +printastype.ret
   
function printastype(s:seq.word) seq.word
  if length.s=1 then s else [last.s,"."_1]+printastype.subseq(s,1,length.s-1)

function gettypelist(s:seq.word) seq.seq.word  gettype(s,1,"",empty:seq.seq.word)

function  gettype( s:seq.word,i:int,result:seq.word,l:seq.seq.word) seq.seq.word
if i > length.s then  l+result
else 
if s_i=","_1 then gettype(s,i+1,"",l+result ) 
else  
   let j=if  i < length.s &and s_(i+1)="."_1 then  i+2 else i+1 
  gettype(s,j,[s_i]+result,  l)
 
Function basesigs(allsrc:seq.seq.word) int
let b=[ 
sig("1","local", "?")
, sig("2","local", "?")
, sig("3","local", "?")
, sig("4","local", "?")
, sig("5","local", "?")
, sig("6","local", "?")
, sig("7","local", "?")
, sig("8","local", "?")
, sig("EXITBLOCK 1","$","?")
, sig("BR 3","$", "?")
, sig("IDXUC(int,int)","builtin", "?") 
, sig("callidx(int,T seq,int)","builtin", "?")
, sig("STKRECORD(int,int)","builtin", "?")
, sig("not(boolean)","builtin","boolean")
, sig("0","$int", "int")
, sig("wordencoding","words", " char seq erecord",lookcloserbit)
, sig55(// "CONSTANT 13107215 13107215" // "CONSTANT 15 15","$constant" , [ lit0, lit0],"?")  
, sig("option(T,word seq)","builtin","$",statebit)  
, sig("+(int, int)","builtin", "int",lookcloserbit)
, sig("=(int, int)","builtin", "boolean",lookcloserbit )
, sig(">(int, int)","builtin", "boolean",lookcloserbit )
, sig("add(T erecord, T encodingrep)","builtin","?",statebit)
, sig("getinstance(T erecord)","builtin","?",statebit)
, sig("getfile(bits seq)","builtin","fileresult",statebit)
, sig("setfld2(T seq, int, T) ","builtin","?",statebit)
, sig("-(int, int)","builtin","int" ,lookcloserbit)
, sig("*(int, int)","builtin","int" ,lookcloserbit)
, sig("/(int, int)","builtin","int" ,lookcloserbit)
, sig("∨(bits, bits)","builtin","bits" ,lookcloserbit)
, sig("∧(bits, bits)","builtin", "bits" ,lookcloserbit)
, sig("<<(bits, int)","builtin","bits" ,lookcloserbit)
, sig(">>(bits, int)","builtin","bits" ,lookcloserbit)
, sig("-(real, real)","builtin", "real",lookcloserbit )
, sig("+(T seq, T seq)","word seq", "word seq" ,lookcloserbit)
, sig("decode(T erecord, T encoding)","char seq encoding", "char seq",lookcloserbit )
, sig("merge(word seq)","words", "word",lookcloserbit )
, sig("encode(T erecord,T)","char seq encoding","char seq encoding",lookcloserbit) 
, sig("decode(char seq erecord, char seq encoding)","char seq encoding","char seq",lookcloserbit)
, sig("encode(char seq  erecord,char seq )","char seq encoding","char seq encoding",lookcloserbit) 
, sig("+(word  seq, word  seq)","word seq", "word seq",lookcloserbit)
, sig("makereal(word seq)", "UTF8", "real",lookcloserbit)
, sig("in(int, int seq)","int seq", "boolean",lookcloserbit)
, sig("in(word, word seq)","word seq", "boolean",lookcloserbit)
] 
let discard2=@(+,processOption,"",allsrc) 
// assert false report discard2 //
 // assert false report @(seperator."&br",decodebits,"",b) //
// assert false report "X"+toword.valueofencoding.optionOp //
// assert length.b=length.baseupbits report "basesig problem" //
 // assert false report decodebits.sig("merge(word seq)","words", "word",lookcloserbit )
 +decodebits.sig("merge(word seq)","words", "word",lookcloserbit) //
 assert 8912911=valueofencoding.lit0 &and lit.0=lit0 report "lit missmatch"+toword.valueofencoding.lit0  
 0 

 
 