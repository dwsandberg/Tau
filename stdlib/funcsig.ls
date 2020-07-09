
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

Function decode(s:sig)fsignrep decode(efsignrep, toencoding.s)


Function emptyprg prg prg.empty:intdict.target


Function hash(a:fsignrep)int  hash(fsig.a + module.a)   

Function =(a:fsignrep, b:fsignrep)boolean   fsig.a = fsig.b ∧ module.a = module.b  

Function returntype(s:fsignrep)seq.word export

Function type:fsignrep internaltype export

Function fsig(fsignrep)seq.word export

Function module(fsignrep)seq.word export

type fsignrep is record fsig:seq.word, module:seq.word,  code:seq.sig, returntype:seq.word,extrabits:bits


 

Function nopara(s:fsignrep)int
 if module.s="$" then toint((fsig.s)_2)  else 
 @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

Function nopara(s:sig)int
   let a = decode.s
    if module.a = "$"then toint.(fsig.a)_2 
    else if last.module.a in  "$constant $fref $words $word $ local"  then 0  
    else nopara.a
  
function counttrue(i:int, b:boolean)int if b then i + 1 else i

type sig is record toencoding:encoding.fsignrep

Function type:sig internaltype export

Function type:prg internaltype export


Function ?(a:sig,b:sig) ordering valueofencoding.toencoding.a ? valueofencoding.toencoding.b


type prg is record translate:intdict.target

type target is record target:sig,code:seq.sig

Function target(target) sig export

Function code(target) seq.sig export

Function constantcode(s:fsignrep) seq.sig
 if module.s in ["$fref" ,"$constant"] then   code.s else empty:seq.sig

Function target(sig,seq.sig) target export

Function type:target internaltype export

use intdict.target

use stacktrace



function  sigandmodule(s:sig) seq.word let x=decode.s  fsig.x+module.x

Function sig(fsig:seq.word,module:seq.word,returntype:seq.word) sig
 sig(encode(efsignrep,fsignrep(fsig,module,empty:seq.sig,returntype,bits.0)))

Function addoptions(code:seq.sig,options:seq.word) seq.sig
 if options ="" then code
 else  
  let codewithoutoptions= if length.code > 0 &and  last.code=optionOp then subseq(code,1,length.code-2) else code
    codewithoutoptions+wordssig.options+optionOp


Function options( code:seq.sig) seq.word  
  if  length.code=0 &or not(last.code=optionOp) then "" else fsig.decode.(code)_(length.code-1)
          
Function   caloptions(p:prg,code:seq.sig,nopara:int,modname:seq.word,fsig:seq.word) seq.word
           let options= options.code  
         if length.code=0 then if  not(modname="builtin" ) then  "STATE" else ""
         else if fsig="in(int, int seq)" &or  fsig="in(word, word seq)" then ""   
         else
           let codeonly= if   last.code=optionOp then subseq(code,1,length.code-2) else code
             let newoptions =options+if not("STATE"_1 in options) &and  @(&or,hasstate,false  ,codeonly ) then "STATE" else ""
        newoptions+if not("NOINLINE"_1 in options)   &and (length.code < 15 &or   issimple(nopara , codeonly )) then "INLINE"
           else "" 
         
Function sig57(fsig:seq.word,modname:seq.word,rettype:seq.word,options:seq.word) sig
 let ex= if "STATE"_1 in options then statebit
  else if "INLINE"_1 in options then inlinebit
  else bits.0
 sig(encode(efsignrep,fsignrep(fsig,modname,empty:seq.sig,rettype,ex)))

 
Function findencode(s:symbol) seq.fsignrep   
findencode(efsignrep,fsignrep(fsig.s,module.s,empty:seq.sig,returntype.s,bits.0))

Function mangledname(s:fsignrep)word 
let a=fsig.s
let j=findindex("("_1, a)  
let name=if j > length.a then a
 else subseq(a, 1, j - 1)
  if length.a < 4 then mangle2( name  ,  module.s,  empty:seq.seq.word )
else
 let b = break(","_1, subseq(a, 1, length.a - 1), j + 1 )
mangle2( name  ,  module.s, b)



function break(w:word, a:seq.word, j:int)seq.seq.word
 let i = findindex(w, a, j)
  if i > length.a then
  if j > length.a then empty:seq.seq.word else [ subseq(a, j, i)]
  else [ subseq(a, j, i - 1)] + break(w, a, i + 1)

Function assignencoding(l:int, s:fsignrep)int 
l+1+toint(  extrabits.s)
 
 
  

Function lookupcode (p:prg, s:sig) seq.target
  lookup(translate.p, valueofencoding.toencoding.s)
 

     use seq.target    
     
     use seq.symbol



Function add(p:prg, s:sig, code:seq.sig)prg
  prg.add(translate.p, valueofencoding.toencoding.s, target(s, code ))
    

Function =(a:sig, b:sig)boolean valueofencoding.toencoding.a = valueofencoding.toencoding.b

Function print(s:seq.sig)seq.word @(+, print,"", s)

Function getsigencoding seq.encodingrep.fsignrep all.getinstance.efsignrep


Function print(s:fsignrep)seq.word
 let t = module.s
  if t = "local"then [ merge("%" + fsig.s)]
  else if t = "$words"then '"' + fsig.s + '"'
  else if t = "$constant" then   let tmp="CONSTANT{"+ print.code.s +"}" 
     if tmp="CONSTANT{ 0 0 } " then "emptyseq"  else tmp
  else if last.t in " $ "then
  if(fsig.s)_1 in "EXITBLOCK LOOPBLOCK CONTINUE BR"then fsig.s + " &br"else fsig.s
  else fsig.s + "[" + t + "]"

   

Function FREFsig(s:sig) sig  
sig(encode(efsignrep,fsignrep("FREF" + sigandmodule.s, "$fref", [ s],"?",bits.0)))  


Function value(s:sig)int toint.(fsig.decode.s)_1

Function lit(i:int)sig  sig([ toword.i],  "int $", "int")

Function block(i:int)sig sig([ "BLOCK"_1,toword.i],  "$",   "?")

Function RECORD(i:int)sig sig([ "RECORD"_1,toword.i],    "$",  "?")

Function loopblock(i:int)sig sig([ "LOOPBLOCK"_1,toword.i],   "$",  "?")

Function apply(i:int)sig  sig([ "APPLY"_1,toword.i],   "$",   "?")

Function continue(i:int)sig  sig([ "CONTINUE"_1,toword.i],    "$",   "?")

Function define(w:word)sig sig([ "DEFINE"_1,w],"$" ,"?")

Function wordsig(w:word) sig sig([ w], "$word", "word")

Function wordssig(w:seq.word) sig sig(w,"$words",  "word seq")
  
Function local(i:int) sig   sig([ toword.i], "local", "?")

Function local(w:word) sig   sig([ w], "local", "?")


Function constant(args:seq.sig) sig
     let txt=@(+,sigandmodule,"",args)
    sig(encode(efsignrep,fsignrep("CONSTANT" + txt, "$constant", args, "?",bits.0)))
     


Function print(s:sig)seq.word print.decode.s

function firstupperbit int 19

Function statebit bits   (bits.1 << firstupperbit  )


function inlinebit bits statebit << 3

Function isconst(s:sig)boolean
module.decode.s in ["$words", "int $", "$word","$constant","$fref" ] 


Function islocal(s:sig)boolean module.decode.s="local"


Function isinline(s:sig)boolean( inlinebit ∧ bits.valueofencoding.toencoding.s) = inlinebit


Function hasstate(s:sig)boolean( statebit ∧ bits.valueofencoding.toencoding.s) =  statebit

Function isblock(s:sig)boolean check(s,"BLOCK")

Function isrecord(s:sig)boolean check(s,"RECORD")

Function isapply(s:sig)boolean check(s,"APPLY")

Function isloopblock(s:sig)boolean check(s,"LOOPBLOCK")

Function isdefine(s:sig)boolean  check(s,"DEFINE")


function check(s:sig, kind:seq.word)boolean
  let t = decode(efsignrep, toencoding.s)
  module.t  = "$" ∧ subseq(fsig.t, 1, 1) = kind



Function local1 sig sig("LOCAL 1","local","?")

Function exit sig  sig("EXITBLOCK 1","$","?")

Function br sig   sig("BR 3","$", "?")

Function IDXUC sig  sig("IDXUC(int,int)","builtin", "?") 

Function CALLIDX sig sig("callidx(int,T seq,int)","builtin", "?")

Function STKRECORD sig sig("STKRECORD(int,int)","builtin", "?")

Function notOp sig sig("not(boolean)","builtin","boolean")

Function lit0 sig sig("0","int $", "int")

Function wordEncodingOp sig sig("wordencoding","words", " char seq erecord")

Function emptyseqOp sig   constant.[ lit0, lit0]

Function optionOp sig sig("option(T,word seq)","builtin","$")  

Function plusOp sig   sig("+(int, int)","builtin", "int")

Function eqOp  sig   sig("=(int, int)","builtin", "boolean")

Function gtOp sig   sig(">(int, int)","builtin", "boolean")
 

  // statebit is set on option so that adding an option doesn't auto add a inline bit //
 
 
Function issimple(nopara:int, code:seq.sig)boolean
    between(length.code, 1, 15)  
 ∧ (nopara = 0 ∨ checksimple(code, 1, nopara, 0))
 

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
     let rep=decode.code_i
     if module.rep="local" then
       let parano=toint.(fsig.rep)_1 
       if parano=last+1 then checksimple(code, i + 1, nopara, last + 1) else false
      else checksimple(code, i + 1, nopara, last)
  

function =(a:bits, b:bits)boolean toint.a = toint.b


Function isinOp(s:sig) boolean
       (fsig.decode.s) in ["in(int, int seq)","in(word, word seq)","=(int,int)","=(word,word)"]

   
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
         sig (fsig.s ,  module.s,returntype.s)


 

 
 