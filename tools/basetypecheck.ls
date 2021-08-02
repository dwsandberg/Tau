#!/usr/local/bin/tau   ; use baseTypeCheck;  resultCheck("stdlib:core")



 
Module baseTypeCheck

use standard

use symbol

use seq.mytype

use set.mytype

use stack.mytype

use seq.symbol

use process.seq.word

use main2

use program

use set.symdef

use seq.symdef

 use intdict.mytype
 
 use set.symbol
 
Function resultCheck( library:seq.word) seq.word 
let p = process.glue2.library
 if aborted.p then message.p else  result.p
 
function glue2(library:seq.word)seq.word let r2 = compilerfront("pass2", library)
checkresults.prg.r2

Function baseTypeCheck( library:seq.word) seq.word 
let p = process.glue.library
 if aborted.p then message.p else  result.p
 
function glue(library:seq.word)  seq.word
  let r2=  compilerfront("pass2",library)
  basetypecheck(prg.r2,alltypes.r2 )
  
function print(s:seq.mytype)seq.word for a ="", e = s do a + print.e /for(a)

Function basetypecheck(r2:seq.symdef, typedict:type2dict)seq.word
 for acc = empty:seq.word, count = 0, s =  r2 do
 let p = process.checkkind(s, typedict)
 let b = if aborted.p then
 " /p ERROR:" + print.sym.s + " /br" + message.p + " /br fullcode"
  + print.code.s
 else result.p
  next(acc + b, if isempty.b then count else count + 1)
 /for(if count = 0 then"Passed Base Type Check"
 else"Base Type Check Failed" + print.count + "Times" + acc /if)
 
 function addlocals(localtypes:intdict.mytype, para:seq.mytype, localno:int, i:int)intdict.mytype
 if i > 0 then addlocals(replace(localtypes, localno, para_i), para, localno - 1, i - 1)else localtypes

function checkkind(s2:symdef, typedict:type2dict)seq.word
 if isconst.sym.s2 ∨ name.sym.s2 ∈ "type]" ∨ isabstract.module.sym.s2 then
 ""
 else
  let codeonly = removeoptions.code.s2
   if length.codeonly = 0 then""
   else
    { assert last.codeonly ≠ Optionsym report"more than one option symbol"}
    let localdict = for acc = empty:intdict.mytype, @e = arithseq(nopara.sym.s2, 1, 1)do
     add(acc, @e, coretype((paratypes.sym.s2)_@e, typedict))
    /for(acc)
    let returntype = coretype(resulttype.sym.s2, typedict)
    for stk = empty:stack.mytype, localtypes = localdict, skip = false, s = codeonly do
      if skip then next(stk, localtypes, false)
      else
       { if s = PreFref then next(push(stk, typeint), localtypes, true)else }
       { assert not.isempty.module.s report"Illformed module on symbol"}
       if isdefine.s then
        assert not.isempty.stk report"Ill formed Define"
        let z = replace(localtypes, value.s, top.stk)
        { assert false report"BB"+ print.s + print.value.s + for acc ="", i = keys.z do acc + toword.i /for(acc)+ for acc ="", i = data.z do acc + print.i /for(acc)}
         next(pop.stk, replace(localtypes, value.s, top.stk), false)
       else if inmodule(s,"$words")then next(push(stk, typeptr), localtypes, false)
       else if inmodule(s,"$real")then next(push(stk, typereal), localtypes, false)
       else if inmodule(s,"$word") ∨ inmodule(s,"$int") ∨ inmodule(s,"$fref")then
        next(push(stk, typeint), localtypes, false)
       else if isRecord.s then
        assert length.toseq.stk ≥ nopara.s report"stack underflow record"
        next(push(pop(stk, nopara.s), typeptr), localtypes, false)
       else if isSequence.s then
        assert length.toseq.stk ≥ nopara.s report"stack underflow sequence"
          next(push(pop(stk, nopara.s), typeptr), localtypes, false)
       else if isloopblock.s then
         let no = nopara.s
         let loc = addlocals(localtypes, top(stk, nopara.s), firstvar.s + no - 1, no)
         next( push(pop(stk, nopara.s),coretype( resulttype.s,typedict)), loc,false)
       else if isexit.s then
        assert top.stk = top.pop.stk report"exit type does not match block type" + print.top.stk + print.top.pop.stk
         next(pop.stk, localtypes, false)
       else if isblock.s then next(stk, localtypes, false)
       else if iscontinue.s then
        assert length.toseq.stk ≥ nopara.s report"stack underflow continue"
        next(pop(stk, nopara.s), localtypes, false)
       else if isstart.s then
        { next(push(stk, resulttype.s), localtypes, false)}
           next( push(stk, if isseq.resulttype.s then typeptr else resulttype.s), localtypes, false)
       else if isbr.s then
        assert top.stk = typeboolean report"if problem"
        + for a ="", e = top(stk, 1)do a + print.e /for(a)
        next(pop.stk, localtypes, false)
       else if islocal.s then
         { assert not.isempty.name2.s report"ill formed local"}
         let localtype = lookup(localtypes, value.s)
         assert not.isempty.localtype report"local not defined" + print.s
           next(push(stk, localtype_1), localtypes, false)
        else if name.s ∈ "packed blockit" ∧ nopara.s = 1 then next(stk, localtypes, false)
        else
         let parakinds = for acc = empty:seq.mytype, @e = paratypes.s do acc + coretype(@e, typedict)/for(acc)
         assert top(stk, nopara.s) = parakinds report" /br symbol type missmatch for" + print.s + " /br stktop" + print.top(stk, nopara.s)
          + " /br parabasetypes"
          + print.parakinds
           next(push(pop(stk, nopara.s), coretype(resulttype.s, typedict)), localtypes, false)
     /for(assert length.toseq.stk = 1 report"Expect one element on stack:" + print.toseq.stk
      assert top.stk = returntype report"Expected return type of" + print.returntype + "but type on stack is" + print.top.stk
      "")

function checkresults(prg:seq.symdef)seq.word
let undefined = for defines = empty:set.symbol, uses = empty:set.symbol, h =  prg  do
 next(defines + sym.h, uses ∪ asset.code.h)
/for(uses - defines - asset.knownsym)
for acc10 =" /p  /p checkresults  /p", h = toseq.undefined do
  if isconst.h
  ∨ name.h = "createthreadY"_1 ∧ isempty(asset.types.h - asset.[ typeint, typereal, typeptr])then
   acc10
  else if name.module.h = "builtin"_1 ∧ name.h ∈ "forexp" then acc10
  else if isabstract.module.h ∨ name.module.h ∈ "$int $define $local $sequence $for $words $loopblock $continue $br $global"
  ∨ name.h ∈ "]"
  ∨ isunbound.h
  ∨ isRecord.h then
   acc10
  else acc10 + print.h   + EOL
 /for("CheckResult:" + if isempty.acc10 then"OK"else acc10 + " /p end checkresults  /p"/if)

function knownsym seq.symbol let typecstr = typeref."cstr fileio."
let typeindex=typeref."index index ."
[ Litfalse, Littrue, PlusOp, NotOp,  Br2(1, 2)
, symbol(moduleref."fileio","tocstr", seqof.typebits, typecstr)
, symbol(moduleref."fileio","createlib2", [ typecstr, typecstr, typeint, seqof.typebits], typeint)
, symbol(moduleref."tausupport","callstack", typeint, seqof.typeint)
, symbol(moduleref."tausupport","dlsymbol", typecstr, typeint)
, symbol(moduleref."tausupport","outofbounds", seqof.typeword)
, symbol(moduleref."tausupport","addresstosymbol2", typeint,seqof.typeref."char standard ."  )
, symbol(moduleref."fileio","getfile", typecstr, typeptr)
, symbol(moduleref."fileio","getbitfile", typecstr, typeptr)
, symbol(moduleref."fileio","getbytefile", typecstr, typeptr)
, symbol(moduleref."fileio","createfile", typeint, seqof.typebits, typecstr, typeint)
, symbol(moduleref."real","sqrt", typereal, typereal)
, symbol(internalmod,"randomfunc", typereal)
, symbol(moduleref."real","intpart", typereal, typeint)
, symbol(moduleref."real","representation", typereal, typeint)
, symbol(moduleref."real","sin", typereal, typereal)
, symbol(moduleref."real","cos", typereal, typereal)
, symbol(moduleref."real","tan", typereal, typereal)
, symbol(moduleref."real","arcsin", typereal, typereal)
, symbol(moduleref."real","arccos", typereal, typereal)
, symbol(moduleref."real","toreal", typeint, typereal)
, symbol(moduleref."real","+", typereal, typereal, typereal)
, symbol(moduleref."real","-", typereal, typereal, typereal)
, symbol(moduleref."real","*", typereal, typereal, typereal)
, symbol(moduleref."real","/", typereal, typereal, typereal)
, symbol(moduleref."real","?", typereal, typereal, typeref."ordering standard . ")
, symbol(moduleref."standard","?", typeint, typeint, typeref."ordering standard . ")
, symbol(moduleref."standard","*", typeint, typeint, typeint)
, symbol(moduleref."standard","-", typeint, typeint, typeint)
, symbol(moduleref."standard","/", typeint, typeint, typeint)
, symbol(moduleref."standard","=", typeint, typeint, typeboolean)
, symbol(moduleref."standard",">", typeint, typeint, typeboolean)
, symbol(moduleref."standard","=", typeboolean, typeboolean, typeboolean)
, symbol(moduleref."bits","xor", typebits, typebits, typebits)
, symbol(moduleref."bits","∧", typebits, typebits, typebits)
, symbol(moduleref."bits","∨", typebits, typebits, typebits)
, symbol(moduleref."bits","<<", typebits, typeint, typebits)
, symbol(moduleref."bits",">>", typebits, typeint, typebits)
, symbol(internalmod,"allocate", typeint, typeptr)
,   GetSeqType ,GetSeqLength
, symbol(internalmod,"getinstance",typeint,typeptr)
, symbol(internalmod,"addencoding",[typeint, typeptr, typeint, typeint],typeint)
, symbol(internalmod,"aborted", typeptr, typeboolean)
, symbol(internalmod,"randomint", typeint, seqof.typeint)
,  {? seqof ptr } symbol(internalmod,"GEP",seqof.typeptr,typeint,typeptr)
, symbol(internalmod,"option",typeint,seqof.typeword,type?) 
, symbol(moduleref."bits","toint", typebyte, typeint)
, symbol(moduleref."bits","toint", typebit, typeint)
, symbol(moduleref("builtin",typereal),"fld", typeptr, typeint, typereal)
, symbol(moduleref("builtin",typeint),"fld", typeptr, typeint, typeint)
, symbol(moduleref("builtin",typeptr),"fld", typeptr, typeint, typeptr)
, symbol(moduleref("builtin",typeboolean),"fld", typeptr, typeint, typeboolean)
, symbol(internalmod ,"idxseq", seqof.typereal, typeint, typereal)
, symbol(internalmod,"idxseq", seqof.typeint, typeint, typeint)
, symbol(internalmod,"idxseq", seqof.typeptr, typeint, typeptr)
, symbol(internalmod,"idxseq", seqof.typeboolean, typeint, typeboolean)
, symbol(internalmod ,"callidx", seqof.typereal, typeint, typereal)
, symbol(internalmod,"callidx", seqof.typeint, typeint, typeint)
, symbol(internalmod,"callidx", seqof.typeptr, typeint, typeptr)
, symbol(internalmod,"callidx", seqof.typeboolean, typeint, typeboolean)
, symbol(internalmod,"packedindex", seqof.typebyte, typeint, typeptr)
, symbol(internalmod,"packedindex", seqof.typebit, typeint, typeptr)
, symbol(internalmod,"packedindex", seqof.typeref."packed2 tausupport .", typeint, typeptr)
, symbol(internalmod,"packedindex", seqof.typeref."packed3 tausupport .", typeint, typeptr)
, symbol(internalmod,"packedindex", seqof.typeref."packed4 tausupport .", typeint, typeptr)
, symbol(internalmod,"packedindex", seqof.typeref."packed5 tausupport .", typeint, typeptr)
, symbol(internalmod,"packedindex", seqof.typeref."packed6 tausupport .", typeint, typeptr)
,{ setSym.typereal, setSym.typeint
, setSym.typeboolean, setSym.typeptr
,} abortsymbol.typereal,abortsymbol.typeint
, abortsymbol.typeboolean,abortsymbol.typeptr
,Exit, Start.typereal, Start.typeint, Start.typeboolean, Start.typeptr, EndBlock]
