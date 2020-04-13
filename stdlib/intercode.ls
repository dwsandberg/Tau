Module intercode

use seq.inst

use otherseq.seq.int

use seq.seq.int

use libscope

use persistant

use stdlib

use seq.symbol

use symbol

use seq.tree.seq.word

use tree.seq.word

type intercode is record  coding:seq.inst, defines:seq.int

Defines are ipointers into coding that indicate which functions are defined.


Codes give a seq of integers which are indices into coding

function intercode(coding:seq.inst, defines:seq.int)intercode export


function code(inst) seq.int export


function coding(intercode)seq.inst export

function defines(intercode)seq.int export

Function type:inst internaltype export

Function type:intercode internaltype export

type inst is record towords:seq.word, flags:seq.word, returntype:mytype, code:seq.int

 Function inst(towords:seq.word, flags:seq.word, returntype:mytype,code:seq.int)inst  export


Function inst(towords:seq.word, flags:seq.word, returntype:mytype)inst inst(towords, flags, returntype, empty:seq.int)


function assignencoding(l:int, a:inst) int l+1

function aseinst(w:seq.word,code:seq.int)int 
valueofencoding.encode(einst, inst(w,"", mytype."?",code))

function aseinst(w:seq.word )int 
let t=encode(einst, inst(w,"", mytype."?" ))
valueofencoding.t


Function mangledname(a:inst)word(towords.a)_1

Function nopara(a:inst)int toint.(towords.a)_2

function flags(a:inst)seq.word export

function towords(a:inst)seq.word export

function returntype(a:inst)mytype export


Function registerword(a:word)int export

Function addobject(flds:seq.int) int export

function addwordseq2(seq.word)int export

Function addliblib( liblib)int export


Function constdata seq.int export

_________________________

type einst is encoding inst

function hash(a:inst)int hash.towords.a

function =(a:inst, b:inst)boolean towords.a = towords.b


function toinst(f:symbol)inst inst([ mangledname.f, toword.nopara.f], flags.f, resulttype.f)

function encode3(f:symbol)int 
valueofencoding.encode(einst,
   inst([ mangledname.f, toword.nopara.f], flags.f, resulttype.f))

function addcodes(allfunctions:symbolset, a:seq.seq.int, f:symbol)seq.seq.int 
let t=prepb(allfunctions, codetree.f)
let s=checkdefines(codetree.f)
// let z=@(+,check(orderadded.einst),empty:seq.word,t)
assert cardinality.asset.z=length.z report "JKLH"+toseq.asset.z +"/" +z+"/"+print.codetree.f
// replace(a, encode3.f,t )


function checkdefines(t:tree.seq.word) seq.word
 let s=@(+,checkdefines,empty:seq.word,sons.t)
if  inst.t="SET"_1 then  
 assert not((label.t)_2 in s) report "problem"
s+(label.t)_2
else if inst.t="LOOPBLOCK"_1 then
   let firstvar=toint.(label((sons.t)_nosons.t))_2
   let no=toint.(label.t)_2
  // assert false report print.t+"/"+(label((sons.t)_nosons.t))_2 //
  let new=   @(+,   toword,"",arithseq(no,1,firstvar))
    assert isempty(asset.new &cap asset.s)report "problem2"
    s+new
else
  s


function check( coding:seq.inst, i:int) seq.word
  if (towords.(coding_i))_1="DEFINE"_1 then [(towords.(coding_i))_2] else empty:seq.word

Function convert2(allfunctions:symbolset, s:seq.symbol)intercode
 let defines = @(+, encode3, empty:seq.int, s)
 let codes=@(addcodes.allfunctions, identity, dseq.empty:seq.int, s)
  intercode(setcode(orderadded.einst,codes, 1,empty:seq.inst),defines)

use set.word
   
function  setcode(coding:seq.inst,codes:seq.seq.int,i:int,result:seq.inst) seq.inst
   if i > length.coding then result
   else  
    let a=coding_i
    if (towords.a)_1 in "CONSTANT FREF" then
      setcode(coding,codes,i+1,result+a)
    else
     setcode(coding,codes,i+1,result+inst(towords.a,flags.a,returntype.a,codes_i))

Function prepb(allfunctions:symbolset, t:tree.seq.word)seq.int
 let inst = inst.t
  if inst in "PARAM"then [ aseinst.[ inst, toword(- toint.arg.t - 1)]]
  else if inst in "LIT LOCAL   WORD FIRSTVAR WORDS"then [ aseinst.label.t]
   else  if inst = "DEFINE"_1 then
  prepb(allfunctions, t_1) + aseinst(label.t)  
  else  if inst = "SET"_1 then
  prepb(allfunctions, t_1) + aseinst("DEFINE" + arg.t) + prepb(allfunctions, t_2)
   + aseinst.[ inst, arg.t]
  else  if inst = "LOOPBLOCK"_1 then
  // number of sons of loop block may have change with optimization //
   let firstvar = arg.last.sons.t
    @(+, prepb.allfunctions, empty:seq.int, subseq(sons.t, 1, nosons.t - 1))
    + aseinst("FIRSTVAR" + firstvar)
    + aseinst.[ inst, toword.nosons.t]
  else if inst = "CRECORD"_1 then 
       let z=   @(+, prepb.allfunctions, empty:seq.int, sons.t)
       assert length.z=nosons.t report "???"
   [ aseinst("CONSTANT" +  @(+,toword,"",z),z)]
   else if inst ="FREF"_1 then
    let z=addfunction(allfunctions,(label.t)_2)
   [ aseinst(label.t,[z])]
  else 
   @(+, prepb.allfunctions, empty:seq.int, sons.t)
   + if inst in "IDXUC EQL CALLIDX STKRECORD CONTINUE RECORD PROCESS2 FINISHLOOP   EXITBLOCK BLOCK BR"
   then [ aseinst.[ inst, toword.nosons.t]]
   else if inst = "STATE"_1 then empty:seq.int
   else
    let s = findencode(einst, inst([ inst, toword.nosons.t],"", mytype."?"))
     [ if length.s = 0 then addfunction(allfunctions,inst)
      else   valueofencoding.encode(einst,s_1)
     ]
     
function addfunction(     allfunctions:symbolset, mangled:word) int
     let s2 = lookupsymbol(allfunctions, mangled)
      if isdefined.s2 then encode3.lookupfunc(allfunctions, mangled)
       else
        let a = codedown.mangled
         assert a_2 = "builtin"report [ mangled] + a_2
           valueofencoding.encode(einst,inst([ mangled, toword(length.a - 2)],"builtin", mytype."?"))   


function astext(coding:seq.inst, i:int)seq.word towords.coding_i

function ithfunc(a:intercode, i:int)seq.word
 towords.(coding.a)_i + @(+, astext.coding.a,"",code.(coding.a)_i) 
 
 + "flags:"
 + flags.(coding.a)_i

Function print(a:intercode)seq.seq.word @(+, ithfunc.a,empty:seq.seq.word, defines.a)