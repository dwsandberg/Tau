module buildtree

use libscope

use passcommon

use seq.bld

use seq.tree.seq.word

use set.symbol

use seq.symbol

use set.word

use stacktrace

use stdlib

use tree.seq.word

use seq.ipair.symbol

use seq.seq.int

use seq.seq.word








/Function print(t:tree.seq.word)seq.word 
 let inst = inst.t 
  @(+, print,"", sons.t)+ if inst in"PARA LIT LOCAL FREF WORD FLAT PARAM FIRSTVAR"
   then [ inst, arg.t]
   else if inst in"CALLB"
   then [ inst, toword.nosons.t, arg.t]
   else if inst ="SET"_1 then [ inst, arg.t]else [ inst, toword.nosons.t]




use newsymbol 


 
use seq.seq.ipair.inst

use seq.ipair.inst

use ipair.inst

use stacktrace


use seq.tree.seq.word

use seq.word

use stack.tree.seq.word

use stdlib

use tree.seq.word

use seq.int

use seq.seq.ipair.symbol

use set.word

use invertedseq.symbol

use ipair.symbol

use seq.mytype

use set.symbol

use graph.word

use set.arc.word

use seq.arc.word

type bld is record state:int, last:word, stk:stack.tree.seq.word, hasstate:boolean

function  towordsx(t:tree.seq.word) word
     { (label.t)_2 }

function addinstruction(nopara:int, b:bld, w:word)bld 
 // state:0 initial, 1 found CALL, 2 at noargs, 4 at funcname in CALL // 
  FORCEINLINE.let newstk = if state.b < 2 ∨ last.b in"FLAT NOINLINE STATE"∧ w ="1"_1 ∨ last.b in"THENBLOCK ELSEBLOCK DEFINE"
    then stk.b 
    else let z = if last.b in"LIT LOCAL FREF WORD PARAM"
     then tree.[last.b, w]
     else if last.b ="PARA"_1 
     then tree.["PARAM"_1, toword(-(toint.w - nopara - 2)-1)]
     else if last.b in"FLD"
     then tree(if w ="1"_1 
      then "IDXUC 0"
      else "getaddressZbuiltinZTzseqZint 0", top(stk.b, 2))
     else if last.b in"SET"
     then tree([last.b, w], top(stk.b, 2))
     else if last.b in"$wordlist"
     then 
        let noelements = toint.w 
       let str= @(+,towordsx,"",top(stk.b,noelements))
        if  // not(str="A Very"+ "special test") // true then
             let prefix = [ tree."LIT 0", tree.["LIT"_1, w]]
          tree("RECORD", prefix  +top(stk.b, noelements)) else  
           tree("WORDS"+w+@(+,towordsx,"",top(stk.b,noelements)))
     else  
      if last.b in"$build"
     then 
       let noelements = toint.w 
      let prefix = [ tree."LIT 0", tree.["LIT"_1, w]]
      tree("RECORD", prefix + removeflat.top(stk.b, noelements))
     else if last.b ="RECORDS"_1 
     then // last element in record becomes the first // 
      tree("RECORD", removeflat([ top.stk.b]+ top(pop.stk.b, toint.w - 1)))
     else if last.b ="FLAT"_1 
     then tree([last.b, w], [ top.stk.b])
     else let sons = top(stk.b, toint.if state.b = 4 then last.b else w)
     tree([if state.b = 4 then w else last.b, if state.b = 4 then last.b else w], if last.b ="RECORD"_1 then removeflat.sons else sons)
    push(pop(stk.b, if last.b in"$build $wordlist RECORD RECORDS"then toint.w else nosons.z), z)
   bld(if state.b = 0 
    then if w ="CALL"_1 then 1 else 2 
    else if state.b = 1 then 4 else 0, w, newstk, hasstate.b ∨ last.b ="STATE"_1 ∧ w ="1"_1)

Function buildcodetree(nopara:int, data:seq.word)tree.seq.word 
 let a = @(addinstruction.nopara, identity, bld(0,"START"_1, empty:stack.tree.seq.word, false), subseq(data, 2, length.data))
  if hasstate.a then tree("STATE", [ top.stk.a])else top.stk.a

function removeflat(s:seq.tree.seq.word)seq.tree.seq.word @(+, processson, empty:seq.tree.seq.word, s)

function processson(t:tree.seq.word)seq.tree.seq.word 
 if inst.t ="FLAT"_1 
  then let firstson = t_1 
   @(+, fixup2.firstson, empty:seq.tree.seq.word, arithseq(toint.arg.t, 1, 0))
  else [ t]

function fixup2(x:tree.seq.word, i:int)tree.seq.word 
 tree( "IDXUC 0", [ x, tree.["LIT"_1, toword.i]])

Function check(a:seq.word, count:int, i:int, ops:seq.word)seq.word 
 if i > length.a 
  then assert i - 1 = length.a report"length overrun"+ a 
   assert count = 1 report"stack should have one"+ toword.count + a 
   ops 
  else if a_i in"PARA LIT CONST LOCAL WORD FREF"
  then check(a, count + 1, i + 2, ops)
  else if a_i ="FLAT"_1 
  then check(a, count, i + 2, ops)
  else if a_i in"SET FLD"
  then check(a, count - 1, i + 2, ops)
  else assert i + 1 ≤ length.a report"overrun"+ a 
  assert isdigits(a_(i + 1))report"expected digits"+ subseq(a, 0, i + 1)
  let args = toint(a_(i + 1))
  assert args ≤ count report"not enough args on stack"+ subseq(a, 0, i + 1)
  if a_i ="CALL"_1 
  then check(a, count - args + 1, i + 3, ops)
  else let new = if a_i in ops then ops else ops + a_i 
  check(a, count - args + 1, i + 2, new)

function isdigits(w:word)boolean @(∧, isdigit, true, decode.w)

function isdigit(i:int)boolean between(i, 48, 57)


_____________


Function prt(f:seq.symbol, i:int)seq.word 
 [ EOL]+ mangledname(f_i)+ towords.resulttype(f_i)+ print.codetree(f_i)

Function filterlib(existing:set.word, f:symbol)seq.symbol 
 if mangledname.f in existing then empty:seq.symbol else [ f]


Function isoption(w:word)boolean 
 w in"PROFILE FORCEINLINE NOINLINE STATE TESTOPT"

Function optdivide(inst:seq.word, i:int)int 
 // look for options at end of instruction // 
  if inst_i ="1"_1 ∧ isoption(inst_(i - 1))then optdivide(inst, i - 2)else i
  
Function roots(isencoding:set.syminfo, m:mod2desc)set.word 
 if isabstract.modname.m ∨ isprivate.m 
  then empty:set.word 
  else @(+, mangled, empty:set.word, toseq.export.m + toseq(defines.m ∩ isencoding))

Function hasErecord(s:syminfo)seq.syminfo 
 if"erecord"_1 in towords.returntype.s then [ s]else empty:seq.syminfo
 
 Function tonewsymbol(alltypes:set.libtype,q:syminfo)    symbol
  let rt = if hasproto.q then protoreturntype.q else returntype.q 
  let myinst = funcfrominstruction(alltypes, instruction.q, replaceT(parameter.modname.q, returntype.q), length.paratypes.q)
  let instend = optdivide(myinst, length.myinst)
  let options = toseq(asset.subseq(myinst, instend+1, length.myinst)-asset."1")
  let newsrc=if subseq(instruction.q, 1, length.instruction.q - length.options)= [ mangled.q] then
   subseq(myinst, 1, instend)+options+"EXTERNAL" 
   else // subseq(myinst, 1, instend)+options //
    printx.buildcodetree(length.paratypes.q , subseq(myinst, 1, instend))+options
  symbol(mangled.q, rt, paratypes.q, name.q, mytype."", newsrc) 
    
 Function printx(t:tree.seq.word)seq.word 
 let inst = inst.t 
  @(+, printx,"", sons.t)+ if inst in"PARA LIT LOCAL FREF WORD FLAT PARAM FIRSTVAR SET"
   then [ inst, arg.t]
   else if inst in "APPLY RECORD CRECORD" then [ inst, toword.nosons.t]
   else [ inst]

/function checkbuild(knownsymbols:symbolset,tr0:tree.seq.word,caller:symbol) seq.word
   let aa=printx.tr0
    let trx=buildcodetreeX(knownsymbols, false, caller, empty:stack.tree.seq.word, 1,aa)
    let bb=printx.trx
     assert aa=bb report "ERR67" +aa+"&br"+bb
     "OK" 

use process.seq.word  

use seq.syminfo
 
 use stacktrace
   
   use stack.tree.seq.word
   
   use set.syminfo
   
   use seq.mod2desc
   
   use opt2

use oseq.int

use passcommon

use buildtree



/use seq.debuginfo

/type debuginfoencoding is encoding debuginfo

/function hash(a:debuginfo)int hash.toword.a

/type debuginfo is record toword:word

/function =(a:debuginfo, b:debuginfo)boolean toword.a = toword.b

function print(g:graph.word)seq.word @(+, p,"", toseq.arcs.g)

function p(a:arc.word)seq.word [ tail.a]+":"+ head.a

function makesym(rt:mytype,name:word) symbol
let d=codedown(name)
  symbol(name,rt, @(+,mytype,empty:seq.mytype,subseq(d,3,length.d)),
  d_1_1,mytype.d_2,"EXTERNAL")

function testx seq.symbol
 let a1=@(+,makesym.mytype."boolean",empty:seq.symbol,
  "Q3EZbuiltinZintZint Q3DZbuiltinZintZint
  Q3FZbuiltinZintZint ")
  let a2=@(+,makesym.mytype."int",a1,
  "Q2BZbuiltinZintZint
  Q2DZbuiltinZintZint 
  Q2AZbuiltinZintZint 
  Q2FZbuiltinZintZint
  hashZbuiltinZint
  randomintZbuiltinZint")
  // assert false report "ERR19"+@(+,print2,"",a2) //
  a2
  
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
 inst("int2realZbuiltinZint 1","builtin", mytype."real"), 
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
 inst("callstackZbuiltinZint 1","builtin", mytype."int seq"), 
 inst("decodeZbuiltinZTzencodingZTzerecord 2","builtin", mytype."T"), 
 inst("mappingZbuiltinZTzerecord 1","builtin", mytype."T seq"), 
 inst("encodeZbuiltinZTZTzerecord 2","builtin", mytype."T encoding"), 
 inst("findencodeZbuiltinZTZTzerecord 2","builtin", mytype."T"), 
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

