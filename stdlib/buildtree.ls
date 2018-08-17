module buildtree

use libscope

use passcommon

use seq.bld

use seq.tree.seq.word

use set.symbol

use seq.symbol

use set.word

use seq.ipair.symbol

use seq.seq.int

use seq.seq.word

/type symbol is record nopara:int, resulttype:mytype, mangledname:word, codetree:tree.seq.word, flags:seq.word

type symbol is record mangledname:word, resulttype:mytype, paratypes:seq.mytype, name:word, modname:mytype, src:seq.word, codetree:tree.seq.word


Function =(a:symbol, b:symbol)boolean mangledname.a = mangledname.b

Function src(symbol)seq.word export

Function name(symbol)word export

Function mangledname(symbol)word export

Function paratypes(symbol)seq.mytype export

Function modname(symbol)mytype export

Function resulttype(symbol)mytype export

Function codetree(f:symbol)tree.seq.word export

Function nopara(s:symbol)int length.paratypes.s

 Function symbol(name:word, modname:mytype, paratypes:seq.mytype, resulttype:mytype, src:seq.word)symbol 
 symbol(mangle(name, modname, paratypes), resulttype, paratypes, name, modname, src)

Function symbol(mangledname:word, resulttype:mytype, paratypes:seq.mytype, name:word, modname:mytype, src:seq.word)symbol
symbol(mangledname, resulttype, paratypes, name, modname, src, tree."default")


Function flags(s:symbol)seq.word flags(src.s, length.src.s)

function flags(src:seq.word, i:int)seq.word 
 if i = 0 
  then""
  else if src_i in"VERYSIMPLE EXTERNAL STATE NOINLINE INLINE SIMPLE COMPLEX FORCEINLINE"
  then flags(src, i - 1)+ src_i 
  else""

Function isundefined(s:symbol)boolean mangledname.s ="undefinedsym"_1

Function isdefined(s:symbol)boolean mangledname.s ≠"undefinedsym"_1


/Function ?(a:symbol, b:symbol)ordering 
 name.a ? name.b ∧ paratypes.a ? paratypes.b ∧ modname.a ? modname.b

/function ?2(a:symbol, b:symbol)ordering name.a ? name.b ∧ paratypes.a ? paratypes.b


Function changesrc(s:symbol, src:seq.word)symbol 
   symbol(mangledname.s, resulttype.s, paratypes.s, name.s, modname.s, src, codetree.s)

Function changecodetree(old:symbol, t:tree.seq.word)symbol 
let oldflags = flags.old
let adjustedflags=flags.old+if inst.t="STATE"_1 then "STATE" else ""
  let functyp = if"FORCEINLINE"_1 in adjustedflags 
   then"INLINE"_1 
   else if"NOINLINE"_1 in adjustedflags 
   then"NOINLINE"_1 
   else functype(t, nopara.old)
  let newflags = [ functyp]+ toseq(asset.adjustedflags - asset."SIMPLE INLINE VERYSIMPLE")
 let newsrc = subseq(src.old, 1, length.src.old - length.oldflags)+ newflags 
symbol(mangledname.old, resulttype.old, paratypes.old, name.old, modname.old, newflags, if inst.t="STATE"_1  then t_1 else t)

Function printdict(s:set.symbol)seq.word @(+, print,"", toseq.s)

Function print(s:symbol)seq.word 
 [ name.s]+"("+ @(seperator.",", print,"", paratypes.s)+")"+ print.resulttype.s +"module:"+ print.modname.s




Function print(t:tree.seq.word)seq.word 
 let inst = inst.t 
  @(+, print,"", sons.t)+ if inst in"PARA LIT LOCAL FREF WORD FLAT PARAM FIRSTVAR"
   then [ inst, arg.t]
   else if inst in"CALLB"
   then [ inst, toword.nosons.t, arg.t]
   else if inst ="SET"_1 then [ inst, arg.t]else [ inst, toword.nosons.t]

/Function print(a:symbol)seq.word 
 {"<"+ mangledname.a + towords.resulttype.a +">"+ print.codetree.a }

--------


Function inst(t:tree.seq.word)word    label(t)_1 

Function arg(t:tree.seq.word)word label(t)_2
 


type ch1result is record nodecount:int, para:seq.int

function combine(nopara:int, a:ch1result, t:tree.seq.word)ch1result 
 if nodecount.a > 15 
  then ch1result(1000, empty:seq.int)
  else let b = ch1(nopara, t)
  ch1result(nodecount.a + nodecount.b, para.a + para.b)

function ch1(nopara:int, t:tree.seq.word)ch1result 
 if inst.t ="PARA"_1 
  then ch1result(1, [ toint.arg.t - nopara - 2])
  else if inst.t ="PARAM"_1 
  then ch1result(1, [ toint.arg.t])
  else if inst.t in"NOINLINE LOOP FINISHLOOP LOOPBLOCK STATE APPLY"
  then ch1result(1000, empty:seq.int)
  else @(combine.nopara, identity, ch1result(1, empty:seq.int), sons.t)

Function functype(t:tree.seq.word, nopara:int)word 
 let a = ch1(nopara, t)
  if nodecount.a > 15 
  then"COMPLEX"_1 
  else if para.a = @(+, identity, empty:seq.int, arithseq(nopara, 1, 1))
  then"SIMPLE"_1 
  else"INLINE"_1

_____________________


Function emptysymbolset symbolset 
 symbolset.dseq.symbol("undefinedsym"_1, mytype."?", empty:seq.mytype,"??"_1, mytype."?","", tree."default")

Function replace(a:symbolset,sym:symbol) symbolset
 symbolset.replace(toseq.a, encoding.mangledname.sym, sym)

type symbolset is record  toseq:seq.symbol



Function lookupfunc(allfunctions:symbolset, f:word)symbol 
   let x= lookupsymbol(allfunctions,f)
    assert isdefined.x report"cannot locate"+ f +stacktrace
x

Function lookupsymbol(a:symbolset, f:word)symbol toseq(a)_encoding.f

 
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
