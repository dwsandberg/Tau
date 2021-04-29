#!/usr/local/bin/tau ; use mylib; bugfind

module baseTypeCheck

use standard

use symbol

use seq.myinternaltype

use seq.mytype

use set.mytype

use stack.mytype

use worddict.mytype

use seq.symbol

use process.seq.word

use seq.seq.word

use process.seq.seq.word

use main2


Function baseTypeCheck( library:seq.word) seq.word let p = process.glue("pass2",library)
 if aborted.p then message.p else print.result.p

 
function glue(stage:seq.word,library:seq.word) seq.seq.word
  let r=  compilerfront(stage,library)
   [baseTypeCheck2(alltypes.r, prg.r)]

function baseTypeCheck2(alltypes:typedict, prg4:program)seq.word
let r = for acc = empty:seq.seq.word, @e = toseq.prg4 do acc + baseTypeCheck(alltypes, prg4, @e)/for(acc)
 if isempty.r then"Passed Base Type Check"
 else
  "Base Type Check Failed" + print.length.r + "Times"
  + for a ="", e = r do a + e /for(a)

function baseTypeCheck(alltypes:typedict, result2:program, s:symbol)seq.seq.word
 let p = process.checkkind(alltypes, result2, s)
  if aborted.p then
  let x = print.s
   [" /p ERROR:" + x + " /br" + message.p + " /br fullcode"
   + for acc ="", @e = code.lookupcode(result2, s)do acc + print.@e /for(acc)]
  else if isempty.result.p then empty:seq.seq.word else [ result.p]

function match(a:mytype, b:mytype)boolean
 a = b ∨ a = typeptr ∧ abstracttype.b /in "seq packed2 packed3 packed4 packed5" 
 ∨ b = typeptr ∧ abstracttype.a /in  "seq packed2 packed3 packed4 packed5" 
 

function match(a:seq.mytype, b:seq.mytype)boolean
 for match = length.a = length.b, idx = 1, e = a while match do next(match(e, b_idx), idx + 1)/for(match)

function addpara(dict:worddict.mytype, alltypes:typedict, paratypes:seq.mytype, i:int)worddict.mytype add(dict, toword.i, getbasetype(alltypes, paratypes_i))

function addlocals(localtypes:worddict.mytype, para:seq.mytype, localno:int, i:int)worddict.mytype
 if i > 0 then addlocals(replace(localtypes, toword.localno, para_i), para, localno - 1, i - 1)
 else localtypes

function print(s:seq.mytype)seq.word for a ="", e = s do a + print.e /for(a)

function checkkind(alltypes:typedict, result2:program, s2:symbol)seq.word
let code = code.lookupcode(result2, s2)
let codeonly = removeoptions.removeoptions.removeoptions.code
 if length.codeonly = 0 then""
 else
  assert last.codeonly ≠ Optionsym report"more than one option symbol"
  let localdict = for acc = emptyworddict:worddict.mytype, @e = arithseq(nopara.s2, 1, 1)do 
  addpara(acc, alltypes, paratypes.s2, @e)/for(acc)
   let returntype= getbasetype(alltypes, resulttype.s2)
 for  stk=empty:stack.mytype,localtypes=localdict,s=codeonly do 
    assert not.isempty.module.s report"Illformed module on symbol"
    if isdefine.s then
     assert not.isempty.stk ∧ length.name.s > 1 report"Ill formed Define"
      next( pop.stk, replace(localtypes,(name.s)_2, top.stk))
    else if module.s = "$words"then
     next( push(stk, mytype."int seq"), localtypes)
    else if module.s = "$real"then next( push(stk, typereal), localtypes)
    else if(module.s)_1 ∈ "$word $int $fref"then next( push(stk, typeint), localtypes)
    else if isRecord.s then
     assert length.toseq.stk ≥ nopara.s report"stack underflow record"
      next( push(pop(stk, nopara.s), typeptr), localtypes)
    else if isSequence.s then
     assert length.toseq.stk ≥ nopara.s report"stack underflow sequence"
      next( push(pop(stk, nopara.s), getbasetype(alltypes, addabstract("seq"_1, parameter.modname.s))), localtypes)
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
     next( push(pop(stk, nopara.s), getbasetype(alltypes, resulttype.s)), loc)
    else if(module.s)_1 = "para"_1 then
     assert length.module.s > 1 report"illform para"
     let x = lookup(localtypes,(module.s)_2)
     assert not.isempty.x report "NOT FOUND PARA"
        next( push(stk, x_1), localtypes)
    else if islocal.s then
     assert not.isempty.name.s report"ill formed local"
     let localtype = lookup(localtypes,(name.s)_1)
      assert not.isempty.localtype report"local not defined" + name.s
       next( push(stk, localtype_1), localtypes)
    else if(name.s)_1 ∈ "packed blockit" ∧ nopara.s = 1 then
     next( stk, localtypes)
    else  if(name.s)_1 ∈ "getseqlength getseqtype setfld blockit   memcpy toseq"then
     next( push(pop(stk, nopara.s), getbasetype(alltypes, resulttype.s)), localtypes)
    else if(name.s)_1 ∈ "IDX GEP idxseq callidx" ∧ length.top(stk, 2) = 2
    ∧ top.stk = typeint
    ∧ top(stk, 2)_1 ∈ [ first.paratypes.s, typeptr]then
     next( push(pop(stk, 2), resulttype.s), localtypes)
    else  if(name.s)_1 = "bitcast"_1 ∧ module.s ≠ "interpreter"
    ∧ nopara.s ≠ 0 then
    let rt = if length.typerep.top.stk > 2 then parameter.top.stk else typeptr
     next( push(pop.stk, rt), localtypes)
    else
     let parakinds = for acc = empty:seq.mytype, @e = paratypes.s do acc + getbasetype(alltypes, @e)/for(acc)
      assert  match(top(stk, nopara.s), parakinds) report
       " /br symbol type missmatch for" + print.s 
       + " /br stktop"
       + print.top(stk, nopara.s)
       + " /br parabasetypes"
       + print.parakinds
         next( push(pop(stk, nopara.s), getbasetype(alltypes, resulttype.s)), localtypes)
       /for   (assert  length.toseq.stk = 1  report "Expect one element on stack:" + print.toseq.stk
       assert  match(top.stk, returntype) report  "Expected return type of" + print.returntype + "but type on stack is"
      + print.top.stk
  "")


