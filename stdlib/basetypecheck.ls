module baseTypeCheck

use standard

use symbol

use seq.myinternaltype

use seq.mytype

use seq.symbol

use set.mytype

use stack.mytype

use worddict.mytype

use process.seq.word

use seq.seq.word

Function baseTypeCheck(alltypes:typedict,prg4:program) seq.word
 let r= for @e ∈ toseq.prg4, acc =empty:seq.seq.word ,,, acc + baseTypeCheck(alltypes, prg4, @e)   
 if isempty.r then "Passed Base Type Check"
 else "Base Type Check Failed "+print.length.r+"Times"+for e &in r ,a="" ,,, a+e 
 

function baseTypeCheck(alltypes:typedict, result2:program, s:symbol)seq.seq.word
 \\ if not(fsig.s ="encode(indexedword erecord, indexedword)")then""else \\
 \\ assert not(name.s ="packed2")report @(+, print,"", code.lookupcode(result2, s))\\
 let p = process.checkkind(alltypes, result2, s)
  if aborted.p then
  let x = print.s
    [" &p ERROR:" + x + " &br" + message.p 
    + " &br fullcode"
     + ( for @e ∈ code.lookupcode(result2, s), acc ="" ,,, acc + print.@e) ]
   else if isempty.result.p then empty:seq.seq.word else [result.p]

  
function checkkind(alltypes:typedict, result2:program, s:symbol)seq.word
 let code = code.lookupcode(result2, s)
 let codeonly = removeoptions.removeoptions.removeoptions.code
  if length.codeonly = 0 then""
  else
   assert last.codeonly ≠ Optionsym report"more than one option symbol"
   let localdict =(for @e ∈ arithseq(nopara.s, 1, 1), acc = emptyworddict:worddict.mytype ,,, addpara(acc, alltypes, paratypes.s, @e))
    \\ assert not(fsig.s ="packed2(typerec2 seq, int)")report"HERE"\\
    if length.code = 2 ∧ fsig.code_2 = "getinstance(T seq)"then""
    else
     let t = ccc(alltypes, codeonly, 1, empty:stack.mytype, localdict)
     assert subseq(t,1,3) = "OK stack:" report t
     assert match(mytype(t << 3),getbasetype( alltypes, resulttype.s)) report 
        "Expected return type of " +print.getbasetype( alltypes, resulttype.s)+ "but type on stack is"+print.mytype(t << 3)
       ""
       
function match(a:mytype,b:mytype) boolean
   a=b &or (a=typeptr &and abstracttype.b="seq"_1) &or (b=typeptr &and abstracttype.a="seq"_1) 
 
function addpara(dict:worddict.mytype, alltypes:typedict, paratypes:seq.mytype, i:int)worddict.mytype
 add(dict, toword.i, getbasetype(alltypes, paratypes_i))

function addlocals(localtypes:worddict.mytype, para:seq.mytype, localno:int, i:int)worddict.mytype
 if i > 0 then addlocals(replace(localtypes, toword.localno, para_i), para, localno - 1, i - 1)
 else localtypes
 
function print(s:seq.mytype) seq.word for e &in s,a="",,, a+print.e

function ccc(alltypes:typedict, code:seq.symbol, i:int, stk:stack.mytype, localtypes:worddict.mytype)seq.word
 if i > length.code then
  if length.toseq.stk &ne 1 then "Expect one element on stack:"+print.toseq.stk
   else "OK stack:" + typerep.top.stk
 else
  let s = code_i
   assert not.isempty.module.s report "Illformed module on symbol"
     if isdefine.s then 
    assert not.isempty.stk ∧ length.name.s > 1 report"Ill formed Define"
      ccc(alltypes, code, i + 1, pop.stk, replace(localtypes,(name.s)_2, top.stk))
   else if module.s = "$words"then ccc(alltypes, code, i + 1, push(stk,mytype."int seq"), localtypes)
   else if module.s = "$real"then ccc(alltypes, code, i + 1, push(stk,mytype."real"), localtypes)
   else if(module.s)_1 ∈ "$word $int $fref"then
   ccc(alltypes, code, i + 1, push(stk,typeint), localtypes)
    else if isRecord.s then
    assert length.toseq.stk ≥ nopara.s report"stack underflow record"
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),typeptr), localtypes)
    else if isSequence.s then
    assert length.toseq.stk ≥ nopara.s report"stack underflow sequence"
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),addabstract("seq"_1,parameter.modname.s)), localtypes)
    else if isexit.s then ccc(alltypes, code, i + 1, stk, localtypes)
    else if iscontinue.s then 
    assert length.toseq.stk ≥ nopara.s report"stack underflow continue"
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),mytype."none"), localtypes)   
   else if isblock.s then
    assert length.toseq.stk ≥ nopara.s report"stack underflow block"
       + ((for @e ∈ subseq(code, 1, i + 1), acc ="",,, acc + print.@e))
       + EOL
       + "point of underflow failure"
    let subblocktypes = asset.top(stk, nopara.s) - asset.[mytype."none"]
    if cardinality.subblocktypes=1 then
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s), subblocktypes_1), localtypes)
    else if cardinality.subblocktypes=2 &and match(subblocktypes_1,subblocktypes_2) then
       ccc(alltypes, code, i + 1, push(pop(stk, nopara.s), 
       if subblocktypes_1=typeptr then subblocktypes_2 else subblocktypes_1 ), localtypes)   
    else  "blockfailure" +  for e &in top(stk, nopara.s),a="",,, a+print.e
    else if isbr.s  then
      assert top(stk, 3) = [mytype."boolean",typeint,typeint  ]  report "if problem"+for e &in top(stk, 3) ,a="",,, a+print.e 
    ccc(alltypes, code, i + 1, push(pop(stk, 3),mytype."none"), localtypes)
    else if isloopblock.s then
    let firstlocal = toint.(fsig.code_(i - 1))_1
     let no = nopara.s - 1
     let loc = addlocals(localtypes, top(stk, nopara.s), firstlocal + no - 1, no)
      ccc(alltypes, code, i + 1, push(pop(stk, nopara.s),mytype."none"), loc)
    else if(module.s)_1 = "para"_1 then
      assert length.module.s > 1 report "illform para"
    let x = lookup(localtypes,(module.s)_2)
      if isempty.x  then"NOT FOUND PARA"else ccc(alltypes, code, i + 1, push(stk, x_1), localtypes)
    else if islocal.s then 
       assert not.isempty.name.s  report "ill formed local"
       let localtype=lookup(localtypes,(name.s)_1)
       assert not.isempty.localtype report "local not defined"+name.s
       ccc(alltypes, code, i + 1, push(stk, localtype_1), localtypes)
    else if (fsig.s)_1 &in "getseqlength getseqtype setfld blockit setfirst memcpy toseq" then
               ccc(alltypes, code, i + 1, push(pop(stk,nopara.s) ,resulttype.s), localtypes)
     else  if (fsig.s)_1  &in "IDX GEP idxseq callidx"  &and length.top(stk,2)=2 &and top.stk=typeint  
     &and ( top(stk, 2)_1 &in [ first.paratypes.s ,typeptr ])  then
           ccc(alltypes, code, i + 1, push(pop(stk, 2),resulttype.s), localtypes)
     else  if (fsig.s)_1  &in "IDX"  &and length.top(stk,2)=2 &and top.stk=typeint  &and abstracttype.top(stk, 2)_1 &in "ptr seq"    then
           ccc(alltypes, code, i + 1, push(pop(stk, 2),parameter.modname.s), localtypes)
      else if (fsig.s)_1="bitcast"_1 &and  module.s &ne  "interpreter"  then 
           let rt= if  length.typerep.top.stk > 2 then  parameter.top.stk else typeptr
              ccc(alltypes, code, i + 1, push(pop(stk),rt), localtypes)
    else
     let parakinds =((for @e ∈ paratypes.s, acc =empty:seq.mytype ,,, acc + getbasetype(alltypes, @e)))
     if top(stk, nopara.s) =parakinds then
     ccc(alltypes, code, i + 1, push(pop(stk, nopara.s), getbasetype(  alltypes, resulttype.s)), localtypes)
      else 
     " &br symbol type missmatch for" + print.s + "at"+ 
     (for @e ∈ subseq(code, i-6,i-1), acc ="",,, acc + print.@e)
     +" &br stktop"
     + print.top(stk, nopara.s)
       + " &br parabasetypes"
       + print.parakinds