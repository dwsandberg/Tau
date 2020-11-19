#!/usr/local/bin/tau

run mylib testnew

module basetypecheck

use seq.myinternaltype

use seq.mytype

use stdlib

use seq.symbol

use symbol

use process.seq.word

use set.word

use stack.word

use worddict.word

Function checkkind2(alltypes:typedict, result2:program, s:symbol)seq.word
 // if not(fsig.s ="encode(indexedword erecord, indexedword)")then""else //
 // assert not(name.s ="packed2")report @(+, print,"", code.lookupcode(result2, s))//
 let p = process.checkkind(alltypes, result2, s)
  if aborted.p then
  let x = print.s
    " &p ERROR:" + x + " &br" + message.p + " &br symbol resultype:"
    + parakind("E" + print.s, alltypes, resulttype.s)
    + "raw"
    + print.resulttype.s
    + " &br fullcode"
    + @(+, print,"", code.lookupcode(result2, s))
  else result.p

function checkkind(alltypes:typedict, result2:program, s:symbol)seq.word
 let code = code.lookupcode(result2, s)
 let codeonly = if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)
 else code
  if length.codeonly = 0 then""
  else
   let localdict = @(addpara(alltypes, paratypes.s), identity, emptyworddict:worddict.word, arithseq(nopara.s, 1, 1))
    // assert not(fsig.s ="packed2(typerec2 seq, int)")report"HERE"//
    if length.code = 2 ∧ fsig.code_2 = "getinstance(T seq)"then""
    else
     let t = ccc(alltypes, codeonly, 1, empty:stack.word, localdict)
      assert t = "OK stack:" + parakind("C" + print.s, alltypes, resulttype.s)report t
       ""

function addpara(alltypes:typedict, paratypes:seq.mytype, dict:worddict.word, i:int)worddict.word
 add(dict, toword.i, parakind("parameters", alltypes, paratypes_i))

function parakinds(alltypes:typedict, sym:symbol)seq.word @(+, parakind("D" + print.sym, alltypes),"", paratypes.sym)

function parakind(place:seq.word, alltypes:typedict, type:mytype)word
 if abstracttype.type in "none int ptr real"then abstracttype.type
 else if abstracttype.type in "encoding"then"int"_1
 else if abstracttype.type in "seq erecord internaltype process encodingstate encodingrep"then"ptr"_1
 else
  let kind = kind.gettypeinfo(alltypes, type)
   assert kind in "int real ptr seq"report"unknown type" + print.type + "place" + place
    if kind in "seq"then"ptr"_1 else kind

function ?(a:myinternaltype, b:myinternaltype)ordering
 name.a ? name.b ∧ parameter.modname.a ? parameter.modname.b

function addlocals(localtypes:worddict.word, para:seq.word, localno:int, i:int)worddict.word
 if i > 0 then addlocals(replace(localtypes, toword.localno, para_i), para, localno - 1, i - 1)
 else localtypes

function ccc(alltypes:typedict, code:seq.symbol, i:int, stk:stack.word, localtypes:worddict.word)seq.word
 if i > length.code then"OK stack:" + toseq.stk
 else
  let s = code_i
   if isapply.s ∧ i - 2 ≤ length.code then
   let k = constantcode.code_(i - 2)
     assert not.isempty.k ∧ length.returntype.k_1 > 0 report"APPLY problem"
     let kind = parakind("apply", alltypes, resulttype.k_1)
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s), kind), localtypes)
   else if isdefine.s then ccc(alltypes, code, i + 1, pop.stk, replace(localtypes,(name.s)_2, top.stk))
   else if module.s = "$words"then ccc(alltypes, code, i + 1, push(stk,"ptr"_1), localtypes)
   else if module.s = "$real"then ccc(alltypes, code, i + 1, push(stk,"real"_1), localtypes)
   else if(module.s)_1 in "$word $lit $fref"then
   ccc(alltypes, code, i + 1, push(stk,"int"_1), localtypes)
   else
    // if s = EqOp then ccc(alltypes, code, i + 1, push(pop(stk, 2),"int"_1), localtypes)else //
    if isrecord.s then ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),"ptr"_1), localtypes)
    else if isexit.s then ccc(alltypes, code, i + 1, stk, localtypes)
    else if iscontinue.s then ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),"none"_1), localtypes)
    else if isblock.s then
    let subblocktypes = asset.top(stk, nopara.s) - asset."none"
      if cardinality.subblocktypes > 1 then"blockfailure" + top(stk, nopara.s)
      else ccc(alltypes, code, i + 1, push(pop(stk, nopara.s), subblocktypes_1), localtypes)
    else if isbr.s ∧ top(stk, 3) = "int int int"then
    ccc(alltypes, code, i + 1, push(pop(stk, 3),"none"_1), localtypes)
    else if isloopblock.s then
    let firstlocal = toint.(fsig.code_(i - 1))_1
     let no = nopara.s - 1
     let loc = addlocals(localtypes, top(stk, nopara.s), firstlocal + no - 1, no)
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),"none"_1), loc)
    else if(module.s)_1 = "para"_1 then
    let x = lookup(localtypes,(module.s)_2)
      if x = ""then"NOT FOUND PARA"else ccc(alltypes, code, i + 1, push(stk, x_1), localtypes)
    else if islocal.s then ccc(alltypes, code, i + 1, push(stk, lookup(localtypes,(name.s)_1)_1), localtypes)
    else if top(stk, nopara.s) = parakinds(alltypes, s)then
    ccc(alltypes, code, i + 1, push(pop(stk, nopara.s), parakind("B" + print.s, alltypes, resulttype.s)), localtypes)
    else
     " &br stack:" + toseq.stk + " &br instruction not handled" + print.s + " &br stktop"
     + top(stk, nopara.s)
     + " &br module"
     + print.modname.s
     + " &br paratypes"
     + @(+, print,"", paratypes.s)
     + " &br parakinds"
     + parakinds(alltypes, s)