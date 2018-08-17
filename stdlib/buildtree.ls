Module cvttoinst

run newimp test1

use buildtree

use libscope

use intercode

use seq.inst

use seq.seq.int

use seq.symbol

use seq.tree.seq.word

use stdlib

use tree.seq.word

type einst is encoding inst

function hash(a:inst)int hash.towords.a

function =(a:inst, b:inst)boolean towords.a = towords.b

function aseinst(w:seq.word)int 
 assert not(w ="FREF")report"problem!"
  encoding.encode(inst.w, einst)

function inst(x:seq.word)inst inst(x,"", mytype."?")

function toinst(f:symbol)inst inst([ mangledname.f, toword.nopara.f], flags.f, resulttype.f)

function encode(x:inst)int encoding.encode(x, einst)

function addcodes(allfunctions:symbolset, a:seq.seq.int, f:symbol)seq.seq.int 
 assert not(label.codetree.f ="default")report"in addcodes" // + print2.f //
   let j = encode.toinst.f 
  assert not.hasexternal.codetree.f report "ERR22" // +print2.f //
  replace(a, j, prepb(allfunctions, codetree.f))

function hasexternal(t:tree.seq.word)boolean 
 if"EXTERNAL"_1 in label.t &and not((label.t)_1 in "WORD WORDS") then true else @(∨, hasexternal, false, sons.t)

Function convert2(allfunctions:symbolset, s:seq.symbol)intercode 
 let discard = @(+, encode, empty:seq.int, initinst)
  let a = @(+, toinst, empty:seq.inst, s)
  let defines = @(+, encode, empty:seq.int, a)
  intercode(@(addcodes.allfunctions, identity, dseq.empty:seq.int, s), mapping.einst, defines)

Function prepb(allfunctions:symbolset, t:tree.seq.word)seq.int 
 let inst = inst.t 
  if inst in"PARAM"
  then [ aseinst.[ inst, toword(-toint.arg.t - 1)]]
  else if inst in"LIT LOCAL FREF WORD FIRSTVAR WORDS"
  then [ aseinst.label.t]
  else if inst ="if"_1 
  then prepb(allfunctions, t_1)+ aseinst."THENBLOCK 1"+ prepb(allfunctions, t_2)+ aseinst."ELSEBLOCK 1"+ prepb(allfunctions, t_3)+ if nosons.t = 3 
   then [ aseinst."if 3"]
   else prepb(allfunctions, t_4)+ aseinst."if 4"
  else if inst ="SET"_1 
  then prepb(allfunctions, t_1)+ aseinst("DEFINE"+ arg.t)+ prepb(allfunctions, t_2)+ aseinst.[ inst, arg.t]
  else if inst ="LOOPBLOCK"_1 
  then // number of sons of loop block may have change with optimization // 
   let firstvar = arg.last.sons.t 
   @(+, prepb.allfunctions, empty:seq.int, subseq(sons.t, 1, nosons.t - 1))+ aseinst("FIRSTVAR"+ firstvar)+ aseinst.[ inst, toword.nosons.t]
  else if inst ="CRECORD"_1 
  then [ aseinst("CONSTANT"+ prep3.t)]
  else @(+, prepb.allfunctions, empty:seq.int, sons.t)+ if inst in"IDXUC EQL CALLIDX STKRECORD CONTINUE RECORD PROCESS2 FINISHLOOP MSET MRECORD"
   then aseinst.[ inst, toword.nosons.t]
   else let s = findencode(inst.[ inst, toword.nosons.t], einst)
   if length.s = 0 
   then encoding.encode(toinst.lookupfunc(allfunctions, inst), einst)
   else encoding.encode(s_1, einst)
   

function initinst seq.inst 
 [ // opGT // 
  inst("Q3EZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // EQL // 
  inst("Q3DZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // ? // 
  inst("Q3FZbuiltinZintZint 2","builtin", mytype."boolean"), 
 // ADD // 
  inst("Q2BZbuiltinZintZint 2","builtin", mytype."int"), 
 // SUB // 
  inst("Q2DZbuiltinZintZint 2","builtin", mytype."int"), 
 // MULT // 
  inst("Q2AZbuiltinZintZint 2","builtin", mytype."int"), 
 // DIV // 
  inst("Q2FZbuiltinZintZint 2","builtin", mytype."int"), 
 inst("hashZbuiltinZint 1","builtin", mytype."int"), 
 inst("randomintZbuiltinZint 1","builtin", mytype."int"), 
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

function prep3(t:tree.seq.word)seq.word 
 @(+, prep3,"", sons.t)+ if nosons.t > 0 then [ inst.t, toword.nosons.t]else label.t

function astext(coding:seq.inst, i:int)seq.word towords(coding_i)

function ithfunc(a:intercode, i:int)seq.word 
 towords(coding(a)_i)+ @(+, astext.coding.a,"", codes(a)_i)+"flags:"+ flags(coding(a)_i)

Function print(a:intercode)seq.word 
 @(seperator."&br &br", ithfunc.a,"", defines.a)




module buildtree

use libscope

use passcommon

use seq.bld

use seq.ch1result

use seq.cnode

use seq.encoding.inst

use seq.symbol

use seq.inst

use seq.ipair.symbol

use seq.seq.int

use seq.seq.word

use seq.tree.seq.word

use seq.word

use stack.tree.seq.word

use stdlib

use tree.seq.word

use seq.int

use seq.seq.ipair.symbol


Function inst(t:tree.seq.word)word  { (label.t)_1 }

Function arg(t:tree.seq.word)word 
 let a =  label.t 
  if length.a < 2 then"0"_1 else a_2


Function cnode(a:word, b:word) seq.word [ a, b]


type symbol is record nopara:int, resulttype:mytype, mangledname:word, codetree:tree.seq.word, flags:seq.word

Function =(a:symbol, b:symbol)boolean mangledname.a = mangledname.b

Function resulttype(f:symbol)mytype export

Function nopara(symbol)int export

Function mangledname(s:symbol)word export

Function flags(s:symbol)seq.word export

Function codetree(f:symbol)tree.seq.word export

Function isundefined(s:symbol)boolean mangledname.s ="undefinedsym"_1

Function isdefined(s:symbol)boolean mangledname.s ≠"undefinedsym"_1

Function lookupsymbol(a:symbolset, f:word)symbol
 let z = find(toinv.a, symbol(f, mytype."", empty:seq.mytype, f, mytype."", ""))
 if length.z=0 then symbol("undefinedsym"_1, mytype."", empty:seq.mytype, "undefinedsym"_1, mytype."", "")
else  value(z_1)

 
Function emptysymbolset symbolset 
symbolset.invertedseq.symbol(0, mytype."int","undefinedsym"_1, tree("default"),"noprofile")


Function symbol(nopara:int, resulttype:mytype, mangledname:word, codetree:tree.seq.word, flags:seq.word)symbol 
 export
 
 use seq.mytype
 
 Function symbol(name:word, modname:mytype, paratypes:seq.mytype, resulttype:mytype, src:seq.word)symbol 
 symbol(length.paratypes,resulttype,mangle(name, modname, paratypes), tree("default"), src)

Function symbol(mangledname:word, resulttype:mytype, paratypes:seq.mytype, name:word, modname:mytype, src:seq.word)symbol 
 symbol(length.paratypes, resulttype, mangledname, tree."default",src)

use set.word

use invertedseq.symbol

use ipair.symbol

Function fixflags(t:tree.seq.word, nopara:int, oldflags:seq.word)seq.word 
 let functyp = if"FORCEINLINE"_1 in oldflags 
   then"INLINE"_1 
   else if"NOINLINE"_1 in oldflags 
   then"NOINLINE"_1 
   else functype(t, nopara)
  toseq(asset.oldflags - asset."SIMPLE INLINE"+ functyp)


Function changecodetree(old:symbol, t:tree.seq.word)symbol 
  let oldflags = flags.old+if inst.t="STATE"_1 then "STATE" else ""
  let functyp = if"FORCEINLINE"_1 in oldflags 
   then"INLINE"_1 
   else if"NOINLINE"_1 in oldflags 
   then"NOINLINE"_1 
   else functype(t, nopara.old)
  let newflags = [ functyp]+ toseq(asset.oldflags - asset."SIMPLE INLINE VERYSIMPLE")
 symbol(nopara.old, resulttype.old, mangledname.old, if inst.t="STATE"_1  then t_1 else t, 
  newflags)



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
     then tree(cnode(last.b, w), top(stk.b, 2))
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
     then tree(cnode(last.b, w), [ top.stk.b])
     else let sons = top(stk.b, toint.if state.b = 4 then last.b else w)
     tree(cnode(if state.b = 4 then w else last.b, if state.b = 4 then last.b else w), if last.b ="RECORD"_1 then removeflat.sons else sons)
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

Function print(t:tree.seq.word)seq.word 
 let inst = inst.t 
  @(+, print,"", sons.t)+ if inst in"PARA LIT LOCAL FREF WORD FLAT PARAM FIRSTVAR"
   then [ inst, arg.t]
   else if inst in"CALLB"
   then [ inst, toword.nosons.t, arg.t]
   else if inst ="SET"_1 then [ inst, arg.t]else [ inst, toword.nosons.t]

Function print(a:symbol)seq.word 
 {"<"+ mangledname.a + towords.resulttype.a +">"+ print.codetree.a }

--------

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

Function hash(f:symbol)int hash.mangledname.f

type symbolset is record toinv:invertedseq.symbol

function symbolset(toinv:invertedseq.symbol) symbolset export

function toinv(symbolset) invertedseq.symbol export

Function lookupfunc(allfunctions:symbolset, f:word)symbol 
 let z = find(toinv.allfunctions, symbol(0, mytype."", f, tree."X X",""))
  assert length.z > 0 report"cannot locate"+ f +stacktrace
  value(z_1)
  
Function  _(ss:symbolset,f: word) symbol  lookupfunc(ss,f)

/Function isdefined(s:symbol)boolean mangledname.s ≠"undefinedsym"_1

Function src(symbol) seq.word "??"

  
Function replace(allfunctions:symbolset,newsymbol:symbol) symbolset
symbolset.add(toinv.allfunctions, encoding.mangledname.newsymbol, newsymbol)



use seq.seq.ipair.inst

use seq.ipair.inst

use ipair.inst

use stacktrace


/Function lookupfunc(allfunctions:invertedseq.symbol, f:word)symbol 
 let z = find(allfunctions, symbol(f, mytype."", empty:seq.mytype, f, mytype."", ""))
  assert length.z > 0 report"cannot locate"+ f +stacktrace
  value(z_1)


