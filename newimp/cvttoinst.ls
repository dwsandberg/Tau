#!/usr/local/bin/tau

Module cvttoinst

run newimp test1


use stdlib

use borrow2

use borrow

use seq.inst

use Symbol

use tree.seq.word

use seq.tree.seq.word

use seq.seq.int

use seq.symbol

type einst is encoding inst

function hash(a:inst)int hash.towords.a

function =(a:inst, b:inst)boolean towords.a = towords.b

function aseinst(w:seq.word)int 
assert not(w="FREF") report "problem!"
encoding.encode(inst.w, einst)

function inst(x:seq.word)inst inst(x,"", mytype."?")

function toinst(f:symbol)inst inst([ mangledname.f, toword.nopara.f], flags.f, resulttype.f)

function encode(x:inst)int encoding.encode(x, einst)


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
  
Function convert2(allfunctions:symbolset, s:seq.symbol)intercode2 
 let discard = @(+, encode, empty:seq.int, initinst)
  let a = @(+, toinst, empty:seq.inst, s)
  let defines = @(+, encode, empty:seq.int, a)
  intercode2(@(addcodes.allfunctions, identity, dseq.empty:seq.int, s), mapping.einst, defines)


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


function initinst seq.inst 
 [ // opGT // 
  inst("Q3EZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // EQL // 
  inst("Q3DZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // ? // 
  inst("Q3FZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // ADD // 
  inst("Q2BZbuiltinZintZint 2","builtin", mytype."int"), 
 // SUB // 
  inst("Q2DZbuiltinZintZint 2","builtin", mytype."int"), 
 // MULT // 
  inst("Q2AZbuiltinZintZint 2","builtin", mytype."int"), 
 // DIV // 
  inst("Q2FZbuiltinZintZint 2","builtin", mytype."int"), 
 inst("hashZbuiltinZint 1","builtin", mytype."int"), 
 inst("randomintZbuiltinZint 1","builtin", mytype."int"), 
 // opGT // 
  inst("Q3EZbuiltinZrealZreal 2","builtin", mytype."boolean"), 
 // EQL // 
  inst("Q3DZbuiltinZrealZreal 2","builtin", mytype."boolean"), 
 // ? // 
  inst("Q3FZbuiltinZrealZreal 2","builtin", mytype."boolean"), 
 // ADD // 
  inst("Q2BZbuiltinZrealZreal 2","builtin", mytype."real"), 
 // SUB // 
  inst("Q2DZbuiltinZrealZreal 2","builtin", mytype."real"), 
 // MULT // 
  inst("Q2AZbuiltinZrealZreal 2","builtin", mytype."real"), 
 // DIV // 
  inst("Q2FZbuiltinZrealZreal 2","builtin", mytype."real"), 
 inst("int2realZbuiltinZint 1","builtin", mytype."real"), 
 inst("intpartZbuiltinZreal 1","builtin", mytype."int"), 
 inst("arccosZbuiltinZreal 1","builtin", mytype."real"), 
 inst("arcsinZbuiltinZreal 1","builtin", mytype."real"), 
 inst("sinZbuiltinZreal 1","builtin", mytype."real"), 
 inst("cosZbuiltinZreal 1","builtin", mytype."real"), 
 inst("tanZbuiltinZreal 1","builtin", mytype."real"), 
 inst("sqrtZbuiltinZreal 1","builtin", mytype."real"), 
 // leftshift // 
  inst("Q3CQ3CZbuiltinZbitsZint 2","builtin", mytype."bits"), 
 // rightshift // 
  inst("Q3EQ3EZbuiltinZbitsZint 2","builtin", mytype."bits"), 
 inst("Q02227ZbuiltinZbitsZbits 2","builtin", mytype."bits"), 
 inst("Q02228ZbuiltinZbitsZbits 2","builtin", mytype."bits"), 
 inst("callstackZbuiltinZint 1","builtin", mytype."int seq"), 
 inst("decodeZbuiltinZTzencodingZTzerecord 2","builtin", mytype."T"), 
 inst("mappingZbuiltinZTzerecord 1","builtin", mytype."T seq"), 
 inst("encodeZbuiltinZTZTzerecord 2","builtin", mytype."T encoding"), 
 inst("findencodeZbuiltinZTZTzerecord 2","builtin", mytype."T"), 
 inst("notZbuiltinZboolean 1","builtin", mytype."boolean"), 
 inst("getaddressZbuiltinZTzseqZint 2","builtin", mytype."T address"), 
 inst("setfldZbuiltinZTzaddressZT 2","builtin", mytype."T address"), 
 inst("allocatespaceZbuiltinZint 1","builtin", mytype."T seq"), 
 inst("libsZbuiltin 0","builtin", mytype."liblib seq"), 
 inst("addresstosymbol2ZbuiltinZint 1","builtin", mytype."int"), 
 inst("createfileZbuiltinZbitszseqZoutputformat 2","builtin", mytype."int"), 
 inst("createlibZbuiltinZbitszseqZbitszseqZoutputformat 3","builtin", mytype."int"), 
 inst("getfileZbuiltinZUTF8 1","builtin", mytype."int"), 
 inst("getfileZbuiltinZbitszseq 1","builtin", mytype."int"), 
 inst("loadlibZbuiltinZUTF8 1","builtin", mytype."int"), 
  inst("loadlibZbuiltinZbitszseq 1","builtin", mytype."int"), 
 inst("unloadlibZbuiltinZUTF8 1","builtin", mytype."int"), 
 inst("unloadlibZbuiltinZbitszseq 1","builtin", mytype."int"), 
 inst("executecodeZbuiltinZUTF8Zintzseq 2","builtin", mytype."int"), 
 inst("executecodeZbuiltinZbitszseqZintzseq 2","builtin", mytype."int"), 
 inst("abortedZbuiltinZTzprocess 1","builtin", mytype."int"), 
 inst("assertZbuiltinZwordzseq 1","builtin", mytype."int"), 
 inst("getmachineinfoZbuiltin 0","builtin", mytype."int"), 
 inst("profileinfoZbuiltin 0","builtin", mytype."int")]

function prep3(t:tree.seq.word)seq.word 
 @(+, prep3,"", sons.t)+  if nosons.t > 0 then [ inst.t,toword.nosons.t] else label.t

function   astext(  coding:seq.inst,i:int) seq.word  towords(coding_i)

function        ithfunc(a:intercode2,i:int) seq.word towords.(coding.a)_i +  @(+,astext.coding.a,"",(codes.a)_i)
+ "flags:"+flags.(coding.a)_i

Function print(a: intercode2)  seq.word @(seperator("&br &br"),ithfunc.a,"",defines.a)
   

Module borrow2  

use passcommon

use reconstruct

/Function emptyintercode intercode2 intercode2(empty:seq.seq.int, empty:seq.inst, empty:seq.int)

defines are indices into coding that indicate which functions are defined and indices into codes that give a seq of integers which are indices into coding

function intercode2(seq.seq.int, seq.inst, seq.int)intercode2 export

function codes(intercode2)seq.seq.int export

function coding(intercode2)seq.inst export

function defines(intercode2)seq.int export

Function inst(towords:seq.word, flags:seq.word, returntype:mytype)inst export

Function mangledname(a:inst)word export

Function nopara(a:inst)int export

function flags(a:inst)seq.word export

function towords(a:inst)seq.word export

function returntype(a:inst)mytype export

use persistant

function addwordseq(linklists2, seq.word) ipair(linklists2) export

Function worddata seq.int export

Function wordcount int export

Function addliblib(linklists2, liblib) ipair.linklists2 export

Function a(linklists2) seq.int export

Function initializer(conststypex:encoding.llvmtype, data:linklists2)int export

