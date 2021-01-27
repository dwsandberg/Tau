#!/usr/local/bin/tau ;  use mylib; bugfind

module baseTypeCheck

use seq.myinternaltype

use seq.mytype

use standard

use seq.symbol

use symbol

use process.seq.word

use set.word

use stack.word

use worddict.word

Function baseTypeCheck(alltypes:typedict, result2:program, s:symbol)seq.word
 // if not(fsig.s ="encode(indexedword erecord, indexedword)")then""else //
 // assert not(name.s ="packed2")report @(+, print,"", code.lookupcode(result2, s))//
 let p = process.checkkind(alltypes, result2, s)
  if aborted.p then
    if (fsig.s)_1 &in "setfld indexseq" then "" else
  let x = print.s
    " &p ERROR:" + x + " &br" + message.p + " &br symbol resultype:"
    + basetype( alltypes, resulttype.s)
    + "raw"
    + print.resulttype.s
    + " &br fullcode"
    + code.lookupcode(result2, s) @ +("", print.@e)
  else result.p
  


function checkkind(alltypes:typedict, result2:program, s:symbol)seq.word
 let code = code.lookupcode(result2, s)
 let codeonly = removeoptions.removeoptions.removeoptions(code)
  if length.codeonly = 0 then""
  else
   assert   last.codeonly &ne Optionsym report "more than one option symbol"
   let localdict = arithseq(nopara.s, 1, 1) @ addpara(emptyworddict:worddict.word, alltypes, paratypes.s, @e)
    // assert not(fsig.s ="packed2(typerec2 seq, int)")report"HERE"//
    if length.code = 2 ∧ fsig.code_2 = "getinstance(T seq)"then""
    else
     let t = ccc(alltypes, codeonly, 1, empty:stack.word, localdict)
      assert t = "OK stack:" + basetype( alltypes, resulttype.s)report t
       ""


 
function basetype(  alltypes:typedict, type:mytype)word
 if abstracttype.type ∈ "none int ptr real"then abstracttype.type
 else // if abstracttype.type ∈ "encoding"then"int"_1
 else // if abstracttype.type ∈ "seq  internaltype process encodingstate encodingrep"then"ptr"_1
 else
  let kind = kind.gettypeinfo(alltypes, type)
    if kind ∈ "seq"then"ptr"_1 else kind

function addpara(dict:worddict.word,alltypes:typedict, paratypes:seq.mytype,  i:int)worddict.word
 add(dict, toword.i, basetype( alltypes, paratypes_i))


function addlocals(localtypes:worddict.word, para:seq.word, localno:int, i:int)worddict.word
 if i > 0 then addlocals(replace(localtypes, toword.localno, para_i), para, localno - 1, i - 1)
 else localtypes

function ccc(alltypes:typedict, code:seq.symbol, i:int, stk:stack.word, localtypes:worddict.word)seq.word
 if i > length.code then"OK stack:" + toseq.stk
 else
  let s = code_i
   assert not.isempty.module.s report "Illformed module on symbol"
     if isdefine.s then 
      assert not.isempty.stk &and length.name.s > 1 report "Ill formed Define"
      ccc(alltypes, code, i + 1, pop.stk, replace(localtypes,(name.s)_2, top.stk))
   else if module.s = "$words"then ccc(alltypes, code, i + 1, push(stk,"ptr"_1), localtypes)
   else if module.s = "$real"then ccc(alltypes, code, i + 1, push(stk,"real"_1), localtypes)
   else if(module.s)_1 ∈ "$word $int $fref"then
   ccc(alltypes, code, i + 1, push(stk,"int"_1), localtypes)
   else
    if isrecord.s then 
      assert length.toseq.stk &ge nopara.s report "stack underflow record"
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),"ptr"_1), localtypes)
    else if isexit.s then ccc(alltypes, code, i + 1, stk, localtypes)
    else if iscontinue.s then 
      assert length.toseq.stk &ge nopara.s report "stack underflow continue"
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),"none"_1), localtypes)
    else if isblock.s then
    let subblocktypes = asset.top(stk, nopara.s) - asset."none"
      if cardinality.subblocktypes > 1 then"blockfailure" + top(stk, nopara.s)
      else 
           assert length.toseq.stk &ge nopara.s report "stack underflow block"+subseq(code,1,i+1) @+("",print.@e)
           +EOL+ "point of underflow failure"
        ccc(alltypes, code, i + 1, push(pop(stk, nopara.s), subblocktypes_1), localtypes)
    else if isbr.s  then
      assert top(stk, 3) = "int int int" report "if problem"+top(stk, 3) 
    ccc(alltypes, code, i + 1, push(pop(stk, 3),"none"_1), localtypes)
    else if isloopblock.s then
    let firstlocal = toint.(fsig.code_(i - 1))_1
     let no = nopara.s - 1
     let loc = addlocals(localtypes, top(stk, nopara.s), firstlocal + no - 1, no)
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),"none"_1), loc)
    else if(module.s)_1 = "para"_1 then
      assert length.module.s > 1 report "illform para"
    let x = lookup(localtypes,(module.s)_2)
      if x = ""then"NOT FOUND PARA"else ccc(alltypes, code, i + 1, push(stk, x_1), localtypes)
    else if islocal.s then 
       assert not.isempty.name.s  report "ill formed local"
       let localtype=lookup(localtypes,(name.s)_1)
       assert not.isempty.localtype report "local not defined"+name.s
       ccc(alltypes, code, i + 1, push(stk, localtype_1), localtypes)
   else  
     let parakinds=paratypes.s @ +("", basetype(  alltypes, @e))
     if top(stk, nopara.s) =parakinds then
    ccc(alltypes, code, i + 1, push(pop(stk, nopara.s), basetype(  alltypes, resulttype.s)), localtypes)
    else
     " &br stack:" + toseq.stk + " &br instruction not handled" + print.s + " &br stktop"
     + top(stk, nopara.s)
     + " &br module"
     + print.modname.s
     + " &br paratypes"
     + paratypes.s @ +("", print.@e)
     + " &br parabasetypes"+ parakinds