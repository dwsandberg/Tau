Module cvttoinst

use encoding.inst

use intercode

use libscope

use seq.inst

use seq.seq.int

use seq.symbol

use seq.tree.seq.word

use stdlib

use symbol

use tree.seq.word

type einst is encoding inst

function hash(a:inst)int hash.towords.a

function =(a:inst, b:inst)boolean towords.a = towords.b

function aseinst(w:seq.word)int 
  findindex(einst,inst.w)

function inst(x:seq.word)inst inst(x,"", mytype."?")

function toinst(f:symbol)inst 
inst([ mangledname.f, toword.nopara.f], flags.f, resulttype.f)

function encode3(f:symbol)int 
findindex(einst,inst([ mangledname.f, toword.nopara.f], flags.f, resulttype.f))



function addcodes(allfunctions:symbolset, a:seq.seq.int, f:symbol)seq.seq.int 
    replace(a, encode3.f, prepb(allfunctions, codetree.f))

Function convert2(allfunctions:symbolset, s:seq.symbol)intercode 
 let discard = @(+, findindex.einst, empty:seq.int, initinst)
   let defines = @(+, encode3, empty:seq.int, s)
  intercode(@(addcodes.allfunctions, identity, dseq.empty:seq.int, s), orderadded.einst, defines)

Function prepb(allfunctions:symbolset, t:tree.seq.word)seq.int 
 let inst = inst.t 
  if inst in"PARAM"
  then [ aseinst.[ inst, toword(-toint.arg.t - 1)]]
  else if inst in"LIT LOCAL FREF WORD FIRSTVAR WORDS"
  then [ aseinst.label.t]
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
   then [ aseinst.[ inst, toword.nosons.t]]
   else if inst ="STATE"_1 
   then empty:seq.int 
   else let s = findencode(einst,inst.[ inst, toword.nosons.t])
   [ if length.s = 0 then 
      encode3.lookupfunc(allfunctions, inst)else      
       index.s_1]

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
  inst("torealZbuiltinZint 1","builtin", mytype."real"), 
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
 inst("xorZbuiltinZbitsZbits 2","builtin", mytype."bits"), 
 inst("callstackZbuiltinZint 1","builtin", mytype."int seq"), 
 inst("getinstanceZbuiltinZTzerecord 1","builtin", mytype."T seq"), 
 inst("encodeZbuiltinZTZTzerecord 2","builtin", mytype."T encoding"), 
  inst("addZbuiltinZTzerecordZTzencodingrep 2","builtin", mytype."int"), 
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
 @(+, prep3,"", sons.t)+ if nosons.t > 0 then [ inst.t, toword.nosons.t]else label.t

function astext(coding:seq.inst, i:int)seq.word towords(coding_i)

function ithfunc(a:intercode, i:int)seq.word 
 towords(coding(a)_i)+ @(+, astext.coding.a,"", codes(a)_i)+"flags:"+ flags(coding(a)_i)

Function print(a:intercode)seq.word 
 @(seperator."&br &br", ithfunc.a,"", defines.a)

