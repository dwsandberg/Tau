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

type intercode is record codes:seq.seq.int, coding:seq.inst, defines:seq.int

Defines are ipointers into coding that indicate which functions are defined.

The field index of inst is a pointer into codes

Codes give a seq of integers which are indices into coding

function intercode(seq.seq.int, seq.inst, seq.int)intercode export

function codes(intercode)seq.seq.int export

function coding(intercode)seq.inst export

function defines(intercode)seq.int export

Function type:inst internaltype export

Function type:intercode internaltype export

type inst is record towords:seq.word, flags:seq.word, returntype:mytype, index:int

Function inst(towords:seq.word, flags:seq.word, returntype:mytype,index:int)inst  export


Function inst(towords:seq.word, flags:seq.word, returntype:mytype)inst inst(towords, flags, returntype, 0)

Function addindex(a:inst, i:int)inst inst(towords.a, flags.a, returntype.a, i)

function assignencoding(l:int, a:inst) int assignrandom(l,a)

function aseinst(w:seq.word)int findindex(einst, inst(w,"", mytype."?"))

Function objectref(b:ipair.linklists2) int export


Function mangledname(a:inst)word(towords.a)_1

Function nopara(a:inst)int toint.(towords.a)_2

function flags(a:inst)seq.word export

function towords(a:inst)seq.word export

function returntype(a:inst)mytype export

function index(a:inst)int export

function addwordseq(linklists2, seq.word)ipair.linklists2 export

Function type:linklists2 internaltype export

Function wordcount int export

Function addliblib(linklists2, liblib)ipair.linklists2 export

/Function a(linklists2)seq.int export

Function length( data:linklists2) int export


Function addconst(l:linklists2, fullinst:seq.word)ipair.linklists2 export

Function registerword(a:word)int export

Function createlinkedlists linklists2 export

Function initializer(conststypex:llvmtype, data:linklists2)int export

Function print(c:intercode, i:inst)seq.word
 towords.i 
 + @(+, towords,"", @(+,_.coding.c, empty:seq.inst,(codes.c)_(index.i))) 
 
 +"flags:"+flags.i


_________________________

type einst is encoding inst

function hash(a:inst)int hash.towords.a

function =(a:inst, b:inst)boolean towords.a = towords.b


function toinst(f:symbol)inst inst([ mangledname.f, toword.nopara.f], flags.f, resulttype.f)

function encode3(f:symbol)int findindex(einst, inst([ mangledname.f, toword.nopara.f], flags.f, resulttype.f))

function addcodes(allfunctions:symbolset, a:seq.seq.int, f:symbol)seq.seq.int replace(a, encode3.f, prepb(allfunctions, codetree.f))

Function convert2(allfunctions:symbolset, s:seq.symbol)intercode
 let defines = @(+, encode3, empty:seq.int, s)
  intercode(@(addcodes.allfunctions, identity, dseq.empty:seq.int, s), orderadded.einst, defines)

Function prepb(allfunctions:symbolset, t:tree.seq.word)seq.int
 let inst = inst.t
  if inst in "PARAM"then [ aseinst.[ inst, toword(- toint.arg.t - 1)]]
  else if inst in "LIT LOCAL FREF WORD FIRSTVAR WORDS"then [ aseinst.label.t]
  else if inst = "if"_1 then
  prepb(allfunctions, t_1) + aseinst."THENBLOCK 1" + prepb(allfunctions, t_2)
   + aseinst."ELSEBLOCK 1"
   + prepb(allfunctions, t_3)
   + if nosons.t = 3 then [ aseinst."if 3"]
   else prepb(allfunctions, t_4) + aseinst."if 4"
  else if inst = "SET"_1 then
  prepb(allfunctions, t_1) + aseinst("DEFINE" + arg.t) + prepb(allfunctions, t_2)
   + aseinst.[ inst, arg.t]
  else if inst = "LOOPBLOCK"_1 then
  // number of sons of loop block may have change with optimization //
   let firstvar = arg.last.sons.t
    @(+, prepb.allfunctions, empty:seq.int, subseq(sons.t, 1, nosons.t - 1))
    + aseinst("FIRSTVAR" + firstvar)
    + aseinst.[ inst, toword.nosons.t]
  else if inst = "CRECORD"_1 then [ aseinst("CONSTANT" + prep3.t)]
  else
   @(+, prepb.allfunctions, empty:seq.int, sons.t)
   + if inst in "IDXUC EQL CALLIDX STKRECORD CONTINUE RECORD PROCESS2 FINISHLOOP MSET MRECORD"
   then [ aseinst.[ inst, toword.nosons.t]]
   else if inst = "STATE"_1 then empty:seq.int
   else
    let s = findencode(einst, inst([ inst, toword.nosons.t],"", mytype."?"))
     [ if length.s = 0 then
     let s2 = lookupsymbol(allfunctions, inst)
       if isdefined.s2 then encode3.lookupfunc(allfunctions, inst)
       else
        let a = codedown.inst
         assert a_2 = "builtin"report [ inst] + a_2
          findindex(einst, inst([ inst, toword(length.a - 2)],"builtin", mytype."?"))
     else index.s_1]

function prep3(t:tree.seq.word)seq.word
 @(+, prep3,"", sons.t)
 + if nosons.t > 0 then [ inst.t, toword.nosons.t]else label.t

function astext(coding:seq.inst, i:int)seq.word towords.coding_i

function ithfunc(a:intercode, i:int)seq.word
 towords.(coding.a)_i + @(+, astext.coding.a,"",(codes.a)_i) + "flags:"
 + flags.(coding.a)_i

Function print(a:intercode)seq.word @(seperator." &br  &br", ithfunc.a,"", defines.a)