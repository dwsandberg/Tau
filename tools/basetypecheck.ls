#!/usr/local/bin/tau   ; use baseTypeCheck; baseTypeCheck("stdlib")



 
module baseTypeCheck

use standard

use symbol

use program

/use symbolsbtc


use seq.myinternaltype

use seq.mytype

use set.mytype

use stack.mytype

use worddict.mytype

use seq.symbol

use process.seq.word

use main2

use program


Function baseTypeCheck( library:seq.word) seq.word 
let p = process.glue( library)
 if aborted.p then message.p else  result.p
 
 Function getbasetype3(a:typedict,t:mytype) mytype getbasetype(a,t)
 
 
 
 
function glue(library:seq.word)  seq.word
  let r2=  compilerfront("pass2",library)
for acc = empty:seq.word,count=0, s = toseq.prg.r2 do 
 let p = process.checkkind(alltypes.r2, prg.r2, s)
 let b=if aborted.p then
     " /p ERROR:" + print.s + " /br" + message.p + " /br fullcode"
   + for acc2 ="", @e = getCode(prg.r2, s)do acc2 + print.@e /for(acc2) 
  else   result.p 
next(acc + b, if isempty.b then count else count+1)/for(
if count=0 then"Passed Base Type Check" else
 "Base Type Check Failed" + print.count + "Times"+
acc)


function match(a:mytype, b:mytype)boolean
 a = b ∨ a = typeptr ∧ isseq.b   
 ∨ b = typeptr ∧ isseq.a 
   /or b =seqof.typeptr /and a /in packedtypes
 /or b =seqof.typeint /and a /in [seqof.typebyte,seqof.typebit]
 /or a =seqof.typeptr /and b /in  packedtypes


function match(a:seq.mytype, b:seq.mytype)boolean
 for match = length.a = length.b, idx = 1, e = a while match do next(match(e, b_idx), idx + 1)/for(match)

function addpara(dict:worddict.mytype, alltypes:typedict, paratypes:seq.mytype, i:int)worddict.mytype add(dict, toword.i, getbasetype3(alltypes, paratypes_i))

function addlocals(localtypes:worddict.mytype, para:seq.mytype, localno:int, i:int)worddict.mytype
 if i > 0 then addlocals(replace(localtypes, toword.localno, para_i), para, localno - 1, i - 1)
 else localtypes

function print(s:seq.mytype)seq.word for a ="", e = s do a + print.e /for(a)

function checkkind(alltypes:typedict, result2:program, s2:symbol)seq.word
let code = getCode(result2, s2)
let codeonly = removeoptions.removeoptions.removeoptions.code
 if length.codeonly = 0 then""
 else
  assert last.codeonly ≠ Optionsym report"more than one option symbol"
  let localdict = for acc = emptyworddict:worddict.mytype, @e = arithseq(nopara.s2, 1, 1)do 
  addpara(acc, alltypes, paratypes.s2, @e)/for(acc)
   let returntype= getbasetype3(alltypes, resulttype.s2)
 for  stk=empty:stack.mytype,localtypes=localdict,s=codeonly do 
    {assert not.isempty.module.s report"Illformed module on symbol"}
    if isdefine.s then
     assert not.isempty.stk   report"Ill formed Define"
      next( pop.stk, replace(localtypes, wordname.s , top.stk))
    else if inmodule(s, "$words") then
     next( push(stk, seqof.typeint), localtypes)
    else if inmodule(s ,"$real") then next( push(stk, typereal), localtypes)
    else if inmodule(s,"$word") /or inmodule(s,"$int") /or inmodule(s,"$fref")  then next( push(stk, typeint), localtypes)
    else if isRecord.s then
     assert length.toseq.stk ≥ nopara.s report"stack underflow record"
      next( push(pop(stk, nopara.s), typeptr), localtypes)
    else if isSequence.s then
     assert length.toseq.stk ≥ nopara.s report"stack underflow sequence"
     assert  parameter.modname.s /in ([typeint,typereal , typeboolean ,typeptr,typebit,typebyte] + packedtypes)
     report "SEQ"+print.parameter.modname.s
      next( push(pop(stk, nopara.s), getbasetype3(alltypes, seqof.parameter.modname.s)), localtypes)
    else if isexit.s then
     assert match(top.stk, top.pop.stk)report"exit type does not match block type" + print.top.stk + print.top.pop.stk
      next( pop.stk, localtypes)
    else if isblock.s then next( stk, localtypes)
    else if iscontinue.s then
     assert length.toseq.stk ≥ nopara.s report"stack underflow continue"
      next( pop(stk, nopara.s), localtypes)
    else if isstart.s then next( push(stk, resulttype.s), localtypes)
    else if isbr.s then
     assert top.stk = typeboolean report"if problem"
     + for a ="", e = top(stk, 1)do a + print.e /for(a)
      next( pop.stk, localtypes)
    else if isloopblock.s then
    let no = nopara.s
    let loc = addlocals(localtypes, top(stk, nopara.s), firstvar.s + no - 1, no)
     next( push(pop(stk, nopara.s), getbasetype3(alltypes, resulttype.s)), loc)
    else if isparameter.s  then
     let x = lookup(localtypes,parameternumber.s)
     assert not.isempty.x report "NOT FOUND PARA"
        next( push(stk, x_1), localtypes)
    else if islocal.s then
     {assert not.isempty.name2.s report"ill formed local"}
     let localtype = lookup(localtypes,(wordname.s) )
      assert not.isempty.localtype report"local not defined" + wordname.s
       next( push(stk, localtype_1), localtypes)
    else if(wordname.s)  ∈ "packed blockit" ∧ nopara.s = 1 then
     next( stk, localtypes)
    else
     let parakinds = for acc = empty:seq.mytype, @e = paratypes.s do acc + getbasetype3(alltypes, @e)/for(acc)
      assert  match(top(stk, nopara.s), parakinds) report
       " /br symbol type missmatch for" + print.s 
       + " /br stktop"
       + print.top(stk, nopara.s)
       + " /br parabasetypes"
       + print.parakinds
         next( push(pop(stk, nopara.s), getbasetype3(alltypes, resulttype.s)), localtypes)
       /for   (assert  length.toseq.stk = 1  report "Expect one element on stack:" + print.toseq.stk
       assert  match(top.stk, returntype) report  "Expected return type of" + print.returntype + "but type on stack is"
      + print.top.stk
  "")


