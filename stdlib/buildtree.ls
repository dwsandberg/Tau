module buildtree


use libscope

use seq.cnode

use seq.func

use seq.seq.word

use seq.tree.cnode

use stack.tree.cnode

use stdlib

use tree.cnode


type cnode is  record towordseq:seq.word

Function inst(t:tree.cnode) word  { (towordseq.label.t)_1 }

Function arg(t:tree.cnode)word {   let a = towordseq.label.t if length( a) < 2 then "0"_1 else  ( a)_2 }

Function inst(a:cnode)word { (towordseq.a)_1 }

Function arg(a:cnode)word {   if length(towordseq.a) < 2 then "0"_1 else  (towordseq.a)_2 }

Function cnode(a:word, b:word)cnode  
cnode.[a,b]  

Function cnode(seq.word) cnode export


Function =(a:cnode, b:cnode)boolean towordseq.a=towordseq.b


type func is record nopara:int, returntype:mytype, mangledname:word, codetree:tree.cnode, flags:seq.word


Function dummyfunc func 
 func(0,mytype."int","dummyfunc"_1, buildcodetree(0,"X LIT 1"),"noprofile")

Function func(nopara:int, returntype:mytype, mangledname:word, codetree:tree.cnode, flags:seq.word)func 
 export

Function returntype(f:func) mytype export

Function nopara(func)int export

Function mangledname(s:func)word  export

Function flags(s:func)seq.word export

Function codetree(f:func)tree.cnode export


function =(a:func, b:func)boolean mangledname.a = mangledname.b

type bld is record state:int,last:word,stk:stack.tree.cnode ,hasstate:boolean

use seq.bld

use seq.word


function  addinstruction(nopara:int,b:bld,w:word) bld
// state :0  initial ,1  found CALL, 2 at noargs, 4 at funcname in CALL //
FORCEINLINE.
  let newstk=if state.b < 2  &or ( last.b in "FLAT NOINLINE STATE" &and w="1"_1 ) &or  last.b in "THENBLOCK ELSEBLOCK DEFINE" then
    stk.b else 
    let z = if last.b in " LIT LOCAL FREF  WORD" then 
           tree.cnode(last.b,w) 
           else if last.b="PARA"_1 then
              tree.cnode("PARAM"_1,toword( toint.w - nopara - 2))
           else if last.b in "FLD" then
            tree(if w="1"_1 then cnode("IDXUC 0") else cnode( "getaddressZbuiltinZTzseqZint 0 "), top(stk.b, 2))
           else if last.b in "SET" then    tree(cnode(last.b,w),top(stk.b,2))
           else if  last.b in"$build $wordlist"
              then let noelements = toint(w)
                   let prefix = [ tree.cnode("LIT 0"), tree.cnode("LIT"_1, w)]
            tree(cnode("RECORD"), prefix + removeflat(top(stk.b, noelements)))
            else if last.b="RECORDS"_1 
  then // last element in record becomes the first // 
    tree(cnode("RECORD"), removeflat([ top.stk.b]+ top(pop.stk.b, toint(w) - 1)))
          else  if last.b ="FLAT"_1 
          then   tree(cnode(last.b, w), [ top.stk.b])
          else  
            let sons = top( stk.b, toint(if state.b=4 then  last.b else w))
           tree(cnode( if state.b=4 then w else last.b,if state.b=4 then last.b else w),   
            if last.b = "RECORD"_1 then          removeflat.sons else sons )
     push(pop(stk.b, if last.b in "$build $wordlist RECORD RECORDS" then toint(w) else  nosons.z),z)
  bld(  if state.b=0 then if w="CALL"_1 then 1 else 2  
        else if state.b=1 then 4 else 0 ,  w , newstk, hasstate.b &or ( last.b = "STATE"_1  &and w="1"_1 ))
 
Function buildcodetree(nopara:int,data:seq.word) tree.cnode 
let a = @(addinstruction(nopara),identity,bld(0,"START"_1,empty:stack.tree.cnode,false),
subseq(data,2,length.data))
 if hasstate.a then tree(cnode("STATE 0"),[top.stk.a]) else top.stk.a
 

 
function removeflat(s:seq.tree.cnode) seq.tree.cnode
 @(+,processson,empty:seq.tree.cnode,s)

function processson(t:tree.cnode) seq.tree.cnode
     if inst.t="FLAT"_1  then
       let firstson = t_1 
       @(+, fixup2.firstson, empty:seq.tree.cnode, arithseq(toint.arg.t, 1, 0))
       else [t]
       

function fixup2(x:tree.cnode, i:int)tree.cnode 
 tree(cnode("IDXUC"_1,"0"_1), [ x, tree.cnode("LIT"_1, toword.i)])


Function check(a:seq.word, count:int, i:int, ops:seq.word)seq.word 
 if i > length.a 
  then assert i - 1 = length.a report"length overrun"+ a 
   assert count = 1 report"stack should have one"+ toword.count + a 
   ops 
  else if a_i in"PARA LIT CONST LOCAL WORD FREF"
  then check(a, count + 1, i + 2, ops)
  else if a_i ="FLAT"_1 
  then check(a, count, i + 2, ops)
  else if a_i in"SET FLD"
  then check(a, count - 1, i + 2, ops)
  else assert i + 1 ≤ length.a report"overrun"+ a 
  assert isdigits(a_(i + 1))report"expected digits"+ subseq(a, 0, i + 1)
  let args = toint(a_(i + 1))
  assert args ≤ count report"not enough args on stack"+ subseq(a, 0, i + 1)
  if a_i ="CALL"_1 
  then check(a, count - args + 1, i + 3, ops)
  else let new = if a_i in ops then ops else ops + a_i 
  check(a, count - args + 1, i + 2, new)
  
function isdigits(w:word)boolean @(∧, isdigit, true, decode.w)

function isdigit(i:int)boolean between(i, 48, 57)


Function print(t:tree.cnode)seq.word 
 let inst = inst.t 
  @(+, print,"", sons.t)+ if inst in"PARA LIT LOCAL FREF WORD FLAT PARAM"
   then [ inst, arg.t]
   else if inst in"CALLB"
   then [ inst, toword.nosons.t, arg.t]
   else if inst ="SET"_1 then [ inst, arg.t]else [ inst, toword.nosons.t]

Function print(a:func)seq.word 
 {"<"+ mangledname.a +  towords.returntype.a +">"+ print.codetree.a }




--------

type ch1result is record nodecount:int, para:seq.int

use seq.ch1result

function combine(nopara:int,a:ch1result,t:tree.cnode)  ch1result 
if nodecount.a > 15 then  ch1result(1000,empty:seq.int) else
let b = ch1(nopara,t)
ch1result(nodecount.a+nodecount.b,para.a+para.b)

function ch1(nopara:int,t:tree.cnode)ch1result 
   if inst.t ="PARA"_1 then ch1result(1,[toint.arg.t - nopara - 2]) 
   else if inst.t="PARAM"_1 then ch1result(1,[toint.arg.t ]) 
  else  if inst.t  in "NOINLINE LOOP FINISHLOOP LOOPBLOCK STATE APPLY" then ch1result(1000,empty:seq.int)
   else @(combine.nopara,identity,ch1result(1,   empty:seq.int),sons.t)
   
Function functype(t:tree.cnode,nopara:int) word
  let a = ch1(nopara,t)
   if nodecount.a > 15  then "COMPLEX"_1
   else  if para.a = @(+,identity,empty:seq.int,arithseq(nopara,-1,-2)) then "SIMPLE"_1
   else "INLINE"_1


_____________________




Function prepb(allfunctions:invertedseq.func,nopara:int, t:tree.cnode)seq.int
  let inst = inst.t 
  if inst in"LIT LOCAL FREF WORD PARAM"
  then [ aseinst([inst, arg.t])]
  else if inst ="if"_1 
  then prepb(allfunctions,nopara, t_1)+ aseinst("THENBLOCK 1")+ prepb(allfunctions,nopara, t_2)+ aseinst("ELSEBLOCK 1")+ prepb(allfunctions,nopara, t_3)+ aseinst("if 3")
  else if inst ="SET"_1 
  then prepb(allfunctions,nopara, t_1)+ aseinst("DEFINE"+ arg.t)+ prepb(allfunctions,nopara, t_2)+ aseinst([inst, arg.t])
  else if inst = "LOOPBLOCK"_1 then 
    let firstvar= arg.last.sons.t
      @(+, prepb(allfunctions,nopara), empty:seq.int, subseq(sons.t, 1, nosons.t-1))+ aseinst("FIRSTVAR"+firstvar)+aseinst([inst, arg.t])
  else if inst ="LOOP"_1 
  then @(+, prepb(allfunctions,nopara), empty:seq.int, subseq(sons.t, 3, nosons.t))+ aseinst("FIRSTVAR"+ arg(t_1))+ aseinst("LOOPBLOCK"+toword(nosons.t - 1))+ prepb(allfunctions,nopara, t_2)+ aseinst("FINISHLOOP 2")
  else if inst ="PARA"_1 
  then assert false report "did not expect PARA"
      [ aseinst("PARAM"+ toword(toint.arg.t - nopara - 2))]
  else if inst ="CRECORD"_1 
  then [aseinst("CONSTANT"+prep3.t)] 
  else  
  @(+, prepb(allfunctions,nopara), empty:seq.int, sons.t)+ if inst in "IDXUC EQL CALLIDX STKRECORD CONTINUE RECORD PROCESS2 FINISHLOOP" then
   aseinst([inst, toword.nosons.t]) else
    let s=findencode(inst([inst, toword.nosons.t]),einst)
    if length.s=0 then
  encoding.encode(toinst.lookupfunc(allfunctions,inst) ,einst)
  else encoding.encode(s_1,einst)
  
  

function initinst seq.inst
   [ // opGT // inst("Q3EZbuiltinZintZint 2 ","builtin", mytype("boolean")),
   //  EQL // inst("Q3DZbuiltinZintZint 2 ","builtin", mytype("boolean")),
   //  ? // inst("Q3FZbuiltinZintZint 2 ","builtin", mytype("boolean")),
   //  ADD // inst("Q2BZbuiltinZintZint 2 ","builtin", mytype("int")), 
   //  SUB // inst("Q2DZbuiltinZintZint 2 ","builtin", mytype("int")),
   //  MULT // inst("Q2AZbuiltinZintZint 2 ","builtin", mytype("int")), 
   //  DIV // inst("Q2FZbuiltinZintZint 2 ","builtin", mytype("int")),
   inst("hashZbuiltinZint 1","builtin", mytype("int")),
     inst("randomintZbuiltinZint 1","builtin", mytype("int")),
   // opGT // inst("Q3EZbuiltinZrealZreal 2 ","builtin", mytype("boolean")),
   //  EQL // inst("Q3DZbuiltinZrealZreal 2 ","builtin", mytype("boolean")),
   //  ? // inst("Q3FZbuiltinZrealZreal 2 ","builtin", mytype("boolean")),
   //  ADD // inst("Q2BZbuiltinZrealZreal 2 ","builtin", mytype("real")), 
   //  SUB // inst("Q2DZbuiltinZrealZreal 2 ","builtin", mytype("real")),
   //  MULT // inst("Q2AZbuiltinZrealZreal 2 ","builtin", mytype("real")), 
   //  DIV // inst("Q2FZbuiltinZrealZreal 2 ","builtin", mytype("real")),
      inst("int2realZbuiltinZint 1 ","builtin", mytype("real")),
      inst("intpartZbuiltinZreal 1","builtin",mytype("int")),
   inst("arccosZbuiltinZreal 1 ","builtin", mytype("real")),
      inst("arcsinZbuiltinZreal 1 ","builtin", mytype("real")),
      inst("sinZbuiltinZreal 1 ","builtin", mytype("real")),
      inst("cosZbuiltinZreal 1 ","builtin", mytype("real")),
      inst("tanZbuiltinZreal 1 ","builtin", mytype("real")),
           inst("sqrtZbuiltinZreal 1 ","builtin", mytype("real")),
   //  leftshift // inst("Q3CQ3CZbuiltinZbitsZint 2 ","builtin", mytype("bits")),
   //  rightshift // inst("Q3EQ3EZbuiltinZbitsZint 2 ","builtin", mytype("bits")),
          inst("Q02227ZbuiltinZbitsZbits 2 ","builtin", mytype("bits")),
           inst("Q02228ZbuiltinZbitsZbits 2 ","builtin", mytype("bits")),
               inst("callstackZbuiltinZint 1","builtin",mytype("int seq")),
              inst("decodeZbuiltinZTzencodingZTzerecord 2","builtin",mytype("T")),
                    inst(" mappingZbuiltinZTzerecord 1","builtin",mytype("T seq")),
              inst("encodeZbuiltinZTZTzerecord 2","builtin",mytype("T encoding")),
                           inst("findencodeZbuiltinZTZTzerecord 2","builtin",mytype("T")),
     inst("notZbuiltinZboolean 1 ","builtin", mytype("boolean")),
     inst("getaddressZbuiltinZTzseqZint 2","builtin", mytype("T address")),
      inst("setfldZbuiltinZTzaddressZT 2","builtin", mytype("T address")),
            inst("allocatespaceZbuiltinZint 1","builtin", mytype("T seq")),
             inst("  libsZbuiltin 0","builtin", mytype("liblib seq")),
              inst("  addresstosymbol2ZbuiltinZint 1","builtin", mytype("int")),
   inst("  createfileZbuiltinZbitszseqZoutputformat 2 ","builtin", mytype("int")),
   inst("  createlibZbuiltinZbitszseqZbitszseqZoutputformat 3 ","builtin", mytype("int")),
   inst("  getfileZbuiltinZUTF8 1 ","builtin", mytype("int")),
   inst("  loadlibZbuiltinZUTF8 1 ","builtin", mytype("int")),
   inst("  unloadlibZbuiltinZUTF8 1 ","builtin", mytype("int")),
   inst("  executecodeZbuiltinZUTF8Zintzseq 2 ","builtin", mytype("int")),
   inst("  abortedZbuiltinZTzprocess 1 ","builtin", mytype("int")),
   inst("  assertZbuiltinZwordzseq  1 ","builtin", mytype("int")),
  inst("  getmachineinfoZbuiltin 0 ","builtin", mytype("int")),
 inst("   profileinfoZbuiltin 0 ","builtin", mytype("int"))
 ]
 
    setfldZbuiltinZTzaddressZT
 
  function prep3(t:tree.cnode)seq.word
  @(+, prep3, "", sons.t)+ [inst.t, if nosons.t > 0 then toword.nosons.t else arg.t]

 
use seq.inst

use passcommon


type einst is encoding inst

function hash(a:inst) int hash(towords.a)

function =(a:inst,b:inst) boolean towords.a=towords.b

function aseinst(w:seq.word) int encoding.encode(inst(w),einst)

use seq.encoding.inst

function inst(x:seq.word) inst inst(x,"",mytype."?")


Function convert2(allfunctions:invertedseq.func ,s:seq.func) intercode2
let discard=@(+,encode,empty:seq.int,initinst)
let a=@(+,toinst,empty:seq.inst,s)
let defines =@(+,encode,empty:seq.int,a)
intercode2(  @(addcodes.allfunctions,identity,dseq(empty:seq.int),s),mapping.einst,defines)

function addcodes(allfunctions:invertedseq.func,a:seq.seq.int,f:func) seq.seq.int
   let j=encode.toinst.f
  replace(a,j, prepb(allfunctions,nopara.f,codetree.f))

use invertedseq.func

use seq.ipair.func

use ipair.func

use seq.seq.int

function encode(x:inst) int encoding.encode(x,einst) 

    function toinst(f:func) inst inst([mangledname.f,toword.nopara.f],flags.f,returntype.f)
                                
Function lookupfunc(allfunctions:invertedseq.func ,f:word) func
  let z = find(allfunctions, func( 0, mytype."", f,  tree.cnode("X"_1,"X"_1), ""))
  assert  length.z > 0 report "cannot locate "+f
  value.z_1


