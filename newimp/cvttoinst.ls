#!/usr/local/bin/tau

Module cvttoinst

run newimp test1


use stdlib

use borrow2

use borrow

use seq.inst2

use Symbol

use tree.seq.word

use seq.tree.seq.word

use seq.seq.int

use seq.symbol



type einst is encoding inst2

function hash(a:inst2)int hash.towords.a

function =(a:inst2, b:inst2)boolean towords.a = towords.b

function aseinst(w:seq.word)int 
assert not(w="FREF") report "problem!"
encoding.encode(inst.w, einst)

function inst(x:seq.word)inst2 inst2(x,"", mytype."?")

function toinst(f:symbol)inst2 inst2([ mangledname.f, toword.nopara.f], flags.f, resulttype.f)

function encode(x:inst2)int encoding.encode(x, einst)


function addcodes(allfunctions:symbolset, a:seq.seq.int, f:symbol)seq.seq.int 
  assert not(label.codetree.f = "default") report "in addcodes"+print2.f
  // assert mangledname.f &ne "arithseqZintzseqZintZTZT"_1 report 
   let k=prepb(allfunctions, codetree.f)
   print.codetree.f+"??"+  @(+,towords,"",  @(+,_(mapping.einst),empty:seq.inst,k)) //
 let j = encode.toinst.f 
   assert not.hasexternal.codetree.f report print.f
  replace(a, j, prepb(allfunctions, codetree.f))
  
function hasexternal(t:tree.seq.word) boolean
if "EXTERNAL"_1 in label.t then true
else @(&or,hasexternal,false,sons.t)
  
Function convert2(allfunctions:symbolset, s:seq.symbol)intercode 
 let discard = @(+, encode, empty:seq.int, initinst)
  let a = @(+, toinst, empty:seq.inst2, s)
  let defines = @(+, encode, empty:seq.int, a)
  intercode(@(addcodes.allfunctions, identity, dseq.empty:seq.int, s), mapping.einst, defines)


Function prepb(allfunctions:symbolset, t:tree.seq.word)seq.int 
 let inst = inst.t 
   if inst in "PARAM" then
    [aseinst.[ inst, toword(-toint.arg.t-1)]]
   else 
    if inst in"LIT LOCAL FREF WORD  FIRSTVAR WORDS"
  then [ aseinst.label.t ]
  else if inst ="if"_1 
  then prepb(allfunctions, t_1)+ aseinst."THENBLOCK 1"+ prepb(allfunctions, t_2)+ aseinst."ELSEBLOCK 1"+ prepb(allfunctions, t_3)+ if nosons.t = 3 
   then [ aseinst."if 3"]
   else prepb(allfunctions, t_4)+ aseinst."if 4"
  else if inst ="SET"_1 
  then prepb(allfunctions, t_1)+ aseinst("DEFINE"+ arg.t)+ prepb(allfunctions, t_2)+ aseinst.[ inst, arg.t]
  else if inst ="LOOPBLOCK"_1 
  then // number of sons of loop block may have change with optimization // 
   let firstvar = arg.last.sons.t 
   @(+, prepb.allfunctions, empty:seq.int, subseq(sons.t, 1, nosons.t - 1))+ aseinst("FIRSTVAR"+ firstvar)+ aseinst.[ inst, toword.nosons.t]
  else if inst ="CRECORD"_1 
  then [ aseinst("CONSTANT"+ prep3.t)]
  else @(+, prepb.allfunctions, empty:seq.int, sons.t)+ if inst in"IDXUC EQL CALLIDX STKRECORD CONTINUE RECORD PROCESS2 FINISHLOOP MSET MRECORD"
   then aseinst.[ inst, toword.nosons.t]
   else let s = findencode(inst.[ inst, toword.nosons.t], einst)
   if length.s = 0 
   then 
      let f=allfunctions_inst
      assert isdefined.f report "in prepb"+label.t
     encoding.encode(toinst.(allfunctions_inst), einst)
   else encoding.encode(s_1, einst)


function initinst seq.inst2 
 [ // opGT // 
  inst2("Q3EZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // EQL // 
  inst2("Q3DZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // ? // 
  inst2("Q3FZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // ADD // 
  inst2("Q2BZbuiltinZintZint 2","builtin", mytype."int"), 
 // SUB // 
  inst2("Q2DZbuiltinZintZint 2","builtin", mytype."int"), 
 // MULT // 
  inst2("Q2AZbuiltinZintZint 2","builtin", mytype."int"), 
 // DIV // 
  inst2("Q2FZbuiltinZintZint 2","builtin", mytype."int"), 
 inst2("hashZbuiltinZint 1","builtin", mytype."int"), 
 inst2("randomintZbuiltinZint 1","builtin", mytype."int"), 
 // opGT // 
  inst2("Q3EZbuiltinZrealZreal 2","builtin", mytype."boolean"), 
 // EQL // 
  inst2("Q3DZbuiltinZrealZreal 2","builtin", mytype."boolean"), 
 // ? // 
  inst2("Q3FZbuiltinZrealZreal 2","builtin", mytype."boolean"), 
 // ADD // 
  inst2("Q2BZbuiltinZrealZreal 2","builtin", mytype."real"), 
 // SUB // 
  inst2("Q2DZbuiltinZrealZreal 2","builtin", mytype."real"), 
 // MULT // 
  inst2("Q2AZbuiltinZrealZreal 2","builtin", mytype."real"), 
 // DIV // 
  inst2("Q2FZbuiltinZrealZreal 2","builtin", mytype."real"), 
 inst2("int2realZbuiltinZint 1","builtin", mytype."real"), 
 inst2("intpartZbuiltinZreal 1","builtin", mytype."int"), 
 inst2("arccosZbuiltinZreal 1","builtin", mytype."real"), 
 inst2("arcsinZbuiltinZreal 1","builtin", mytype."real"), 
 inst2("sinZbuiltinZreal 1","builtin", mytype."real"), 
 inst2("cosZbuiltinZreal 1","builtin", mytype."real"), 
 inst2("tanZbuiltinZreal 1","builtin", mytype."real"), 
 inst2("sqrtZbuiltinZreal 1","builtin", mytype."real"), 
 // leftshift // 
  inst2("Q3CQ3CZbuiltinZbitsZint 2","builtin", mytype."bits"), 
 // rightshift // 
  inst2("Q3EQ3EZbuiltinZbitsZint 2","builtin", mytype."bits"), 
 inst2("Q02227ZbuiltinZbitsZbits 2","builtin", mytype."bits"), 
 inst2("Q02228ZbuiltinZbitsZbits 2","builtin", mytype."bits"), 
 inst2("callstackZbuiltinZint 1","builtin", mytype."int seq"), 
 inst2("decodeZbuiltinZTzencodingZTzerecord 2","builtin", mytype."T"), 
 inst2("mappingZbuiltinZTzerecord 1","builtin", mytype."T seq"), 
 inst2("encodeZbuiltinZTZTzerecord 2","builtin", mytype."T encoding"), 
 inst2("findencodeZbuiltinZTZTzerecord 2","builtin", mytype."T"), 
 inst2("notZbuiltinZboolean 1","builtin", mytype."boolean"), 
 inst2("getaddressZbuiltinZTzseqZint 2","builtin", mytype."T address"), 
 inst2("setfldZbuiltinZTzaddressZT 2","builtin", mytype."T address"), 
 inst2("allocatespaceZbuiltinZint 1","builtin", mytype."T seq"), 
 inst2("libsZbuiltin 0","builtin", mytype."liblib seq"), 
 inst2("addresstosymbol2ZbuiltinZint 1","builtin", mytype."int"), 
 inst2("createfileZbuiltinZbitszseqZoutputformat 2","builtin", mytype."int"), 
 inst2("createlibZbuiltinZbitszseqZbitszseqZoutputformat 3","builtin", mytype."int"), 
 inst2("getfileZbuiltinZUTF8 1","builtin", mytype."int"), 
 inst2("getfileZbuiltinZbitszseq 1","builtin", mytype."int"), 
 inst2("loadlibZbuiltinZUTF8 1","builtin", mytype."int"), 
  inst2("loadlibZbuiltinZbitszseq 1","builtin", mytype."int"), 
 inst2("unloadlibZbuiltinZUTF8 1","builtin", mytype."int"), 
 inst2("unloadlibZbuiltinZbitszseq 1","builtin", mytype."int"), 
 inst2("executecodeZbuiltinZUTF8Zintzseq 2","builtin", mytype."int"), 
 inst2("executecodeZbuiltinZbitszseqZintzseq 2","builtin", mytype."int"), 
 inst2("abortedZbuiltinZTzprocess 1","builtin", mytype."int"), 
 inst2("assertZbuiltinZwordzseq 1","builtin", mytype."int"), 
 inst2("getmachineinfoZbuiltin 0","builtin", mytype."int"), 
 inst2("profileinfoZbuiltin 0","builtin", mytype."int")]

function prep3(t:tree.seq.word)seq.word 
 @(+, prep3,"", sons.t)+  if nosons.t > 0 then [ inst.t,toword.nosons.t] else label.t

function   astext(  coding:seq.inst2,i:int) seq.word  towords(coding_i)

function        ithfunc(a:intercode,i:int) seq.word towords.(coding.a)_i +  @(+,astext.coding.a,"",(codes.a)_i)
+ "flags:"+flags.(coding.a)_i

Function print(a: intercode)  seq.word @(seperator("&br &br"),ithfunc.a,"",defines.a)
   

Module borrow2  

/use passcommon

use reconstruct

use stdlib


type intercode is record codes:seq.seq.int, coding:seq.inst2, defines:seq.int


defines are indices into coding that indicate which functions are defined and indices into codes that give a seq of integers which are indices into coding

function intercode(seq.seq.int, seq.inst2, seq.int)intercode export

function codes(intercode)seq.seq.int export

function coding(intercode)seq.inst2 export

function defines(intercode)seq.int export


type inst2 is record towords:seq.word, flags:seq.word, returntype:mytype


Function inst2(towords:seq.word, flags:seq.word, returntype:mytype)inst2 export

Function mangledname(a:inst2)word towords(a)_1

Function nopara(a:inst2)int toint(towords(a)_2)

function flags(a:inst2)seq.word export

function towords(a:inst2)seq.word export

function returntype(a:inst2)mytype export




use persistant

function addwordseq(linklists2, seq.word) ipair(linklists2) export

Function worddata seq.int export

Function wordcount int export

Function addliblib(linklists2, liblib) ipair.linklists2 export

Function a(linklists2) seq.int export

Function initializer(conststypex:encoding.llvmtype, data:linklists2)int export

