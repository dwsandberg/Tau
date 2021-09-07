#!/usr/local/bin/tau   ; use baseTypeCheck;  resultCheck("stdlib ")
 
Module baseTypeCheck

use standard

use symbol2

use seq.mytype

use set.mytype

use stack.mytype

use seq.symbol

use process.seq.word

use main2

use set.symdef

use seq.symdef

use set.symbol
 
type typemap is key:int,value:mytype
   
function lookup( a:set.typemap,key:int) set.typemap
lookup(a, typemap(key,typeint) ) 

Function ?(a:typemap,b:typemap) ordering key.a ? key.b 

use set.typemap
 
use seq.typemap

 
 
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
  basetypecheck(prg.r2,typedict.r2 )
  
function print(s:seq.mytype)seq.word for a ="", e = s do a + print.e /for(a)

Function basetypecheck(r2:seq.symdef, typedict:typedict)seq.word
 for acc = empty:seq.word, count = 0, s =  r2 do
 let p = process.checkkind(s, typedict)
 let b = if aborted.p then
 " /p ERROR:" + print.sym.s + " /br" + message.p + " /br fullcode"
  + print.code.s
 else result.p
  next(acc + b, if isempty.b then count else count + 1)
 /for(if count = 0 then"Passed Base Type Check"
 else"Base Type Check Failed" + print.count + "Times" + acc /if)
 
 function addlocals(localtypes:set.typemap, para:seq.mytype, localno:int, i:int)set.typemap
 if i > 0 then addlocals(  typemap( localno, para_i) /cup localtypes, para, localno - 1, i - 1)else localtypes

function checkkind(s2:symdef, typedict:typedict)seq.word
 if isconst.sym.s2 ∨ name.sym.s2 ∈ "type]" ∨ isabstract.module.sym.s2 then
 ""
 else
  let codeonly = removeoptions.code.s2
   if length.codeonly = 0 then""
   else
    { assert last.codeonly ≠ Optionsym report"more than one option symbol"}
    let localdict = for acc = empty:set.typemap, @e = arithseq(nopara.sym.s2, 1, 1)do
       typemap(@e, coretype((paratypes.sym.s2)_@e, typedict)) /cup acc 
    /for(acc)
    let returntype = coretype(resulttype.sym.s2, typedict)
    for stk = empty:stack.mytype, localtypes = localdict, skip = false, s = codeonly do
      if skip then next(stk, localtypes, false)
      else
       { if s = PreFref then next(push(stk, typeint), localtypes, true)else }
       { assert not.isempty.module.s report"Illformed module on symbol"}
       if isdefine.s then
        assert not.isempty.stk report"Ill formed Define"
        let z = typemap(  value.s, top.stk) /cup localtypes
        { assert false report"BB"+ print.s + print.value.s + for acc ="", i = keys.z do acc + toword.i /for(acc)+ for acc ="", i = data.z do acc + print.i /for(acc)}
         next(pop.stk, typemap( value.s, top.stk) /cup localtypes, false)
       else if iswords.s then next(push(stk, typeptr), localtypes, false)
       else if isRealLit.s then next(push(stk, typereal), localtypes, false)
       else if isword.s ∨  isIntLit.s ∨ isFref.s then
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
         let localtype = lookup( localtypes,value.s )
         assert not.isempty.localtype report"local not defined" + print.s
           next(push(stk, value.localtype_1), localtypes, false)
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
/for(uses \ defines \ asset.knownsym)
for acc10 =" /p  /p checkresults  /p", h = toseq.undefined do
  if isconst.h
  ∨ name.h = "createthreadY"_1 ∧ isempty(asset.types.h \ asset.[ typeint, typereal, typeptr])then
   acc10
  else if  isBuiltin.h ∧ name.h ∈ "forexp" then acc10
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
, symbol(internalmod,"tocstr", seqof.typebits, typecstr)
, symbol(internalmod,"createlib2", [ typecstr, typecstr, typeint, seqof.typebits], typeint)
, symbol(internalmod,"callstack", typeint, seqof.typeint)
, symbol(internalmod,"dlsymbol", typecstr, typeint)
, symbol(internalmod,"outofbounds", seqof.typeword)
, symbol(internalmod,"addresstosymbol2", typeint,seqof.typeref."char standard ."  )
, symbol(internalmod,"getfile", typecstr, typeptr)
, symbol(internalmod,"getbitfile", typecstr, typeptr)
, symbol(internalmod,"getbytefile", typecstr, typeptr)
, symbol(internalmod,"createfile", typeint, seqof.typebits, typecstr, typeint)
, symbol(internalmod,"loadlib", typecstr, typeint)
, symbol(internalmod,"unloadlib2", typecstr, typeint)
, symbol(internalmod,"sqrt", typereal, typereal)
, symbol(internalmod,"randomfunc", typereal)
,  symbol(internalmod,"intpart", typereal, typeint)
, symbol(internalmod,"representation", typereal, typeint)
, symbol(internalmod,"sin", typereal, typereal)
, symbol(internalmod,"cos", typereal, typereal)
, symbol(internalmod,"tan", typereal, typereal)
, symbol(internalmod,"arcsin", typereal, typereal)
, symbol(internalmod,"arccos", typereal, typereal)
, symbol(internalmod,"toreal", typeint, typereal)
, symbol(internalmod,"+", typereal, typereal, typereal)
, symbol(internalmod,"-", typereal, typereal, typereal)
, symbol(internalmod,"*", typereal, typereal, typereal)
, symbol(internalmod,"/", typereal, typereal, typereal)
, symbol(internalmod,"?", typereal, typereal, typeref."ordering standard . ")
,  symbol(internalmod,"?", typeint, typeint, typeref."ordering standard . ")
, symbol(internalmod,"*", typeint, typeint, typeint)
, symbol(internalmod,"-", typeint, typeint, typeint)
, symbol(internalmod,"/", typeint, typeint, typeint)
, symbol(internalmod,"=", typeint, typeint, typeboolean)
, symbol(internalmod,">", typeint, typeint, typeboolean)
, symbol(internalmod,"=", typeboolean, typeboolean, typeboolean)
, symbol(internalmod,"xor", typebits, typebits, typebits)
, symbol(internalmod,"∧", typebits, typebits, typebits)
, symbol(internalmod,"∨", typebits, typebits, typebits)
, symbol(internalmod,"<<", typebits, typeint, typebits)
, symbol(internalmod,">>", typebits, typeint, typebits)
, symbol(internalmod,"allocate", typeint, typeptr)
,   GetSeqType ,GetSeqLength
, symbol(internalmod,"getmachineinfo",typeptr)
, symbol(internalmod,"getinstance",typeint,typeptr)
, symbol(internalmod,"addencoding",[typeint, typeptr, typeint, typeint],typeint)
, symbol(internalmod,"processisaborted", typeptr, typeboolean)
, symbol(internalmod,"randomint", typeint, seqof.typeint)
,  {? seqof ptr } symbol(internalmod,"GEP",seqof.typeptr,typeint,typeptr)
,symbol(internalmod,"GEP",seqof.typeint,typeint,typeint)
, symbol(internalmod,"option",typeint,seqof.typeword,type?) 
, symbol(internalmod,"toint", typebyte, typeint)
, symbol(internalmod,"toint", typebit, typeint) 
,  symbol(builtinmod(typereal),"fld", typeptr, typeint, typereal)
, symbol(builtinmod(typeint),"fld", typeptr, typeint, typeint)
, symbol(builtinmod(typeptr),"fld", typeptr, typeint, typeptr)
, symbol(builtinmod(typeboolean),"fld", typeptr, typeint, typeboolean)
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
