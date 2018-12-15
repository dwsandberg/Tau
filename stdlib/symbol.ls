module symbol

use libscope

use processtypes

use seq.callsresult

use seq.libsym

use seq.mytype

use seq.syminfo

use set.syminfo

use set.word

use seq.word

use stdlib

use deepcopy.callsresult

Function CALLcode(info:syminfo)seq.word 
 // let inst = if name.info ="encodeword"_1 ∧ returntype.info = mytype."word"then"encodeword 1"else instruction.info // 
  let inst = instruction.info 
  if length.inst > 0 ∧ inst_1 in"USECALL ERECORD UNBOUND PRECORD"
  then [ if isabstract.modname.info then"CALLB"_1 else"CALL"_1, 
  toword.length.paratypes.info, 
  mangled.info]
  else inst

Function FREFcode(info:syminfo)seq.word 
 if isabstract.modname.info 
  then ["FREFB"_1, mangled.info]
  else ["FREF"_1, mangled.info]

  
function FREFdeepcopy(type:mytype) seq.word
 { if isabstract.type then "FREFB" else "FREF" }+mangle("deepcopy"_1, mytype(towords.type+"deepcopy"), [ mytype."T"])
  
function CALLdeepcopy(type:mytype) seq.word
  { if isabstract.type then "CALLB 1" else "CALL 1" }+mangle("deepcopy"_1, mytype(towords.type+"deepcopy"), [ mytype."T"])


function invertedseqadd(type:mytype) seq.word
 { if isabstract.type then "FREFB" else "FREF" }+mangle("add"_1, mytype(towords.type+"invertedseq"), [ mytype."T invertedseq", mytype."int", mytype."T"])


function invertedseqlookup(type:mytype) seq.word
 { if isabstract.type then "FREFB" else "FREF" }+mangle("lookup"_1, mytype(towords.type+"invertedseq"), [ mytype."T", mytype."T invertedseq"])

 replaceTsyminfo(type, syminfo("lookup"_1, mytype."T invertedseq", [ mytype."T", mytype."T invertedseq"], mytype."int","USECALL"))
 


Function deepcopybody(alltypes:set.libtype, type:mytype)seq.word 
 if type = mytype."int"∨ abstracttype.type ="encoding"_1 
  then"PARAM 1"
  else if abstracttype.type ="seq"_1 
  then let typepara = parameter.type 
   let pseqidx =  { if isabstract.type then "FREFB" else "FREF" }+mangle("_"_1, mytype(towords.type+"seq"),  [ mytype."T pseq", mytype."int"])
  let cat =
    { if isabstract.type then "FREFB" else "FREF" }+mangle("+"_1, mytype(towords.type+"seq"), [ mytype."T seq", mytype."T"])
   let blockit =   { if isabstract.type then "CALLB 1" else "CALL 1" }+
   mangle("blockit"_1, mytype(" int blockseq"), [  mytype."T seq"])
    {"LIT 0 LIT 0 RECORD 2 PARAM 1"+ FREFdeepcopy.typepara  + cat + pseqidx +"APPLY 5"+ blockit } 
  else let subs = deepcopytypes2(alltypes, type)
  if length.subs = 0 
  then"PARAM 1"
  else if length.subs = 1 
  then if subs_1 = type 
   then"PARAM 1"
   else"PARAM 1"+ CALLdeepcopy(subs_1)
  else @(+, subfld.subs, empty:seq.word, arithseq(length.subs, 1, 1))+"RECORD"+ toword.length.subs

function subfld(subs:seq.mytype, i:int)seq.word 
 {"PARAM 1 LIT"+ toword(i - 1)+"IDXUC 2"+ CALLdeepcopy(subs_i)}

Function codingrecord(sym:syminfo)seq.word 
 let encodingtype = parameter.returntype.sym 
 let invertedseqadd=
 { if isabstract.encodingtype then "FREFB" else "FREF" }+mangle("add"_1, mytype(towords.encodingtype+"invertedseq"), [ mytype."T invertedseq", mytype."int", mytype."T"])
let invertedseqlookup=
 { if isabstract.encodingtype then "FREFB" else "FREF" }+mangle("lookup"_1, mytype(towords.encodingtype+"invertedseq"), [ mytype."T", mytype."T invertedseq"])
  FREFdeepcopy.encodingtype +invertedseqlookup + invertedseqadd +(if name.sym ="wordencoding"_1 then"LIT 1"else"LIT 0")+"WORD"+ mangled.sym +(if instruction(sym)_1 ="ERECORD"_1 
   then"LIT 0"
   else"LIT 1") +"RECORD 6 NOINLINE 1"
   
Function noparameters(s:syminfo)int length.paratypes.s

   
Function processcode(sym:syminfo,pcode:seq.word) seq.word 
let noargs = noparameters.sym FREFdeepcopy.returntype.sym + 
   FREFdeepcopy.mytype."word seq"+ FREFcode.sym +"LIT"+ toword.noargs + pcode+
   "RECORD"+ toword(noargs + 4)+"PROCESS2 1"

type callsresult is record state:int, result:set.word

function callsadd(c:callsresult, w:word)callsresult 
 FORCEINLINE.let state = state.c 
  let newstate = if state = // base state // 0 
   then if w ="WORD"_1 
    then 1 
    else if w ="FREF"_1 
    then 4 
    else if w ="CALL"_1 
    then 3 
    else // assert not(w in"BUILDSEQ CALLB FREFB BUILD TSIZE")report"not expecting instruction"+ w +"in compiled code"// 
    0 
   else if state = // CALL arg // 3 then 4 else // state = 1 // 0 
  callsresult(newstate, if state = // func arg of CALL or FREF // 4 then result.c + w else result.c)

Function calls(l:syminfo)set.word 
 // returns all functions that are called directly called by l // 
  result.@(callsadd, identity, callsresult(0, empty:set.word), instruction.l)

Function compileinstance(alltypes:set.libtype, lookup:set.syminfo, w:word)seq.syminfo 
 let info = tosyminfo.w 
  let c = findencode(libsym(mytype."?", w,""), libsymencoding)
  if not.isempty.c 
  then empty:seq.syminfo 
  else if not.isinstance.modname.info 
  then // we only compiled modinstances // empty:seq.syminfo 
  else let manglep = mangle(protoname.info, mytype("T"+ abstracttype.modname.info), protoparatypes.info)
  let lc = decode(encode(libsym(mytype."?", manglep,""), libsymencoding), libsymencoding)
  assert not("UNBOUND"_1 in instruction.lc)report"U2"+ w 
   let inst=
     if abstracttype.modname.info = "deepcopy"_1 &and name.info="deepcopy"_1 then "USECALL"+ deepcopybody(alltypes, parameter.modname.info)
  else   funcfrominstruction(alltypes, removeB(alltypes, lookup, modname.info, instruction.lc, 1), replaceT(parameter.modname.info, returntypeold.lc), length.paratypes.info)
  let x = changeinstruction(replaceTsyminfo(parameter.modname.info, syminfo.lc), inst)
  let b = encode(libsym(returntype.x, mangled.x, instruction.x), libsymencoding)
  @(+, compileinstance(alltypes, lookup), [ x], toseq.calls.x)

function removeB(lookup:set.syminfo, with:mytype, w:word)word 
 let s = tosyminfo.w 
  assert isabstract.modname.s report"should be abstract"+ print.s 
  if not.hasproto.s ∧ last.towords.modname.s ="unbound"_1 
  then let name = if length.paratypes.s = 0 then replaceT(replaceT(with, parameter.modname.s), name.s)else name.s 
   let paras = @(+, replaceT.with, empty:seq.mytype, paratypes.s)
   let e = findelement2(lookup, syminfo(name, paras))
   assert cardinality.e = 1 report if cardinality.e = 0 
    then"unbound not defined?"+ formatcall(name, paras)
    else"multiple definitions of unbound"+ formatcall(name, paras)+"in"+ @(+, print,"", @(+, modname, empty:seq.mytype, toseq.e))
   mangled(e_1)
  else mangled.replaceTsyminfo(with, s)

function removeB(alltypes:set.libtype, lookup:set.syminfo, modname:mytype, w:seq.word, i:int)seq.word 
 // remove abstract calls from code // 
  // assert not(modname = mytype."T")report"with must not contain T in call to removeB"// 
  if i > length.w 
  then assert not("UNBOUND"_1 in w)report"U3"
   w 
  else if w_i ="CALLB"_1 
  then let code = ["CALL"_1, w_(i + 1), removeB(lookup, parameter.modname, w_(i + 2))]
   let new = subseq(w, 1, i - 1)+ code + subseq(w, i + 3, length.w)
   removeB(alltypes, lookup, modname, new, i + length.code)
  else if w_i ="FREFB"_1 
  then let code = ["FREF"_1, removeB(lookup, parameter.modname, w_(i + 1))]
   let new = subseq(w, 1, i - 1)+ code + subseq(w, i + 2, length.w)
   removeB(alltypes, lookup, modname, new, i + 2)
  else if w_i ="TSIZE"_1 
  then let k = toword(LIT.sizeoftype(alltypes, parameter.modname)* toint(w_(i + 1))+ toint(w_(i - 1)))
   let new = subseq(w, 1, i - 2)+ k + subseq(w, i + 2, length.w)
   removeB(alltypes, lookup, modname, new, i)
  else // if w_i ="DEEPCOPY"_1 
  then"USECALL"+ deepcopybody(alltypes, parameter.modname)
  else // if w_i ="BUILDSEQ"_1 
  then let name ="_"_1 
   let paras = [ mytype(towords.parameter.modname + w_(i + 2)), mytype."int"]
   let e = findelement2(lookup, syminfo(name, paras))
   assert cardinality.e = 1 report if cardinality.e = 0 
    then"unbound not defined?"+ formatcall(name, paras)
    else"multiple definitions of unbound"+ formatcall(name, paras)+"in"+ @(+, print,"", @(+, modname, empty:seq.mytype, toseq.e))
   let code = ["FREF"_1, mangled(e_1),"RECORDS"_1, toword(toint(w_(i + 1))+ 1)]
   let new = subseq(w, 1, i - 1)+ code + subseq(w, i + 3, length.w)
   removeB(alltypes, lookup, modname, new, i + length.code)
  else if w_i ="WORD"_1 
  then removeB(alltypes, lookup, modname, w, i + 2)
  else removeB(alltypes, lookup, modname, w, i + 1)

---------------------------

