module symbol


use libscope


use processtypes

use seq.libsym

use seq.mytype

use seq.syminfo

use set.syminfo

use set.word

use stdlib

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

Function finddeepcopyfunction(type:mytype)syminfo 
 let a = syminfo("deepcopy"_1, mytype."T blockseq", [ mytype."T"], mytype."T","DEEPCOPY 1")
  if mytype."T"= type 
  then a 
  else changeinstruction(replaceTsyminfo(type, a),"USECALL")

Function invertedseqadd(type:mytype)syminfo 
 replaceTsyminfo(type, syminfo("add"_1, mytype."T invertedseq", [ mytype."T invertedseq", mytype."int", mytype."T"], mytype."T invertedseq","USECALL"))

Function invertedseqlookup(type:mytype)syminfo 
 replaceTsyminfo(type, syminfo("lookup"_1, mytype."T invertedseq", [ mytype."T", mytype."T invertedseq"], mytype."int","USECALL"))

Function blockitfunc syminfo 
 replaceTsyminfo(mytype."int", syminfo("blockit"_1, mytype."T blockseq", [ mytype."T seq"], mytype."T seq","USECALL"))

Function pseqidxfunc(type:mytype)syminfo 
 replaceTsyminfo(type, syminfo("_"_1, mytype."T seq", [ mytype."T pseq", mytype."int"], mytype."T","USECALL"))

Function catfunc(type:mytype)syminfo 
 replaceTsyminfo(type, syminfo("+"_1, mytype."T seq", [ mytype."T seq", mytype."T"], mytype."T seq","USECALL"))

Function deepcopybody(alltypes:set.libtype, type:mytype)seq.word 
 if type = mytype."int"∨ abstracttype.type ="encoding"_1 
  then"PARA 1"
  else if abstracttype.type ="seq"_1 
  then let typepara = parameter.type 
   let dc = FREFcode.finddeepcopyfunction.typepara 
   let xx = FREFcode.pseqidxfunc.typepara 
   let cat = FREFcode.catfunc.type 
   let blockit = CALLcode.blockitfunc 
   {"LIT 0 LIT 0 RECORD 2 PARA 1"+ dc + cat + xx +"APPLY 5"+ blockit } 
  else let subs = deepcopytypes2(alltypes, type)
  if length.subs = 0 
  then"PARA 1"
  else if length.subs = 1 
  then if subs_1 = type 
   then"PARA 1"
   else"PARA 1"+ CALLcode.finddeepcopyfunction(subs_1)
  else @(+, subfld.subs, empty:seq.word, arithseq(length.subs, 1, 1))+"RECORD"+ toword.length.subs

Function subfld(subs:seq.mytype, i:int)seq.word 
 {"PARA 1 LIT"+ toword(i - 1)+"IDXUC 2"+ CALLcode.finddeepcopyfunction(subs_i)}

Function codingrecord(sym:syminfo)seq.word 
 let encodingtype = parameter.returntype.sym 
  FREFcode.finddeepcopyfunction.encodingtype + FREFcode.invertedseqlookup.encodingtype + FREFcode.invertedseqadd.encodingtype + if encodingtype = mytype."int seq"
   then"LIT 1 WORD word LIT 0 RECORD 6 NOINLINE 1"
   else"LIT 0 WORD"+ mangled.sym +(if instruction(sym)_1 ="ERECORD"_1 
    then"LIT 0"
    else"LIT 1")+"RECORD 6 NOINLINE 1"

Function calls(l:syminfo)set.word 
 // returns all functions that are called directly called by l // 
  gather2(instruction.l, 1, empty:set.word)

function gather2(s:seq.word, i:int, r:set.word)set.word 
 if i > length.s 
  then r 
  else if s_i ="WORD"_1 
  then gather2(s, i + 2, r)
  else if s_i ="CALL"_1 
  then let x = s_(i + 2)
   gather2(s, i + 3, r + x)
  else if s_i ="FREF"_1 
  then let x = s_(i + 1)
   gather2(s, i + 2, r + x)
  else assert not(s_i in"BUILDS CALLB FREFB BUILD TSIZE")report"not expecting instruction"+ s_i +"in compiled code"+ s 
  gather2(s, i + 1, r)

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
  let inst = funcfrominstruction(alltypes, removeB(alltypes, lookup, modname.info, instruction.lc, 1), replaceT(parameter.modname.info, returntypeold.lc), length.paratypes.info)
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
  else if w_i ="DEEPCOPY"_1 
  then"USECALL"+ deepcopybody(alltypes, parameter.modname)
  else if w_i ="WORD"_1 
  then removeB(alltypes, lookup, modname, w, i + 2)
  else removeB(alltypes, lookup, modname, w, i + 1)

---------------------------

