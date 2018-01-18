module buildtree

use constant

use libscope

use seq.cnode

use seq.func

use seq.seq.word

use seq.tree.cnode

use stack.tree.cnode

use stdlib

use tree.cnode

type cnode is record inst:word, arg:word

Function inst(cnode)word export

Function arg(cnode)word export

Function =(a:cnode, b:cnode)boolean inst.a = inst.b ∧ arg.b = arg.a

type func is record nopara:int, symboltext:seq.word, number:word, codetree:tree.cnode, profile:seq.word

Function funckey(w:word)int encoding.w

Function key(f:func)int funckey.number.f

Function dummyfunc func 
 func(0,"dummyfunc","0"_1, buildcodetree("LIT 1", 1),"")

Function func(nopara:int, symboltext:seq.word, number:word, codetree:tree.cnode, profile:seq.word)func 
 export

Function symboltext(f:func)seq.word export

Function nopara(func)int export

Function number(s:func)word export

Function profile(s:func)seq.word export

Function codetree(f:func)tree.cnode export

Function replacecodetree(f:func, new:tree.cnode)func 
 func(nopara.f, symboltext.f, number.f, new, profile.f)

function =(a:func, b:func)boolean number.a = number.b

Function buildcodetree(a:seq.word, i:int)tree.cnode 
 let b = check(a, 0, 1,"")
  buildcodetree(a, empty:stack.tree.cnode, i)

function pushconst(a:seq.word, f:stack.tree.cnode, i:int)stack.tree.cnode 
 push(f, tree.cnode(a_i, a_(i + 1), 0))

function scanconst(a:seq.word, i:int)int 
 if i + 2 > length.a 
  then i 
  else if a_(i + 2)in"LIT CONST WORD FREF"then scanconst(a, i + 2)else i

function buildcodetree(a:seq.word, f:stack.tree.cnode, i:int)tree.cnode 
 if i > length.a 
  then top.f 
  else if a_i in"LIT CONST WORD FREF"
  then // we look for a const here by scanning forward // 
   let j = scanconst(a, i)
   if j + 1 < length.a ∧ a_(j + 2)in"$build $wordlist RECORD"
   then let len = toint(a_(j + 3))
    if len * 2 > j - i + 2 
    then // len of record is greater than length of constants // 
     buildcodetree(a, @(pushconst.a, identity, f, arithseq((j - i + 2)/ 2, 2, i)), j + 2)
    else // not all constants may be part of record so must calculate prefix // 
    let prefix = @(pushconst.a, identity, f, arithseq((j - i)/ 2 + 1 - len, 2, i))
    let const =(if a_(j + 2)="RECORD"_1 
     then"RECORD"+ a_(j + 3)
     else"RECORD"+ toword(len + 2)+"LIT 0 LIT"+ a_(j + 3))+ subseq(a, j - 2 * len + 2, j + 1)
    buildcodetree(a, push(prefix, tree.cnode("CONST"_1, addconst.const, 0)), j + 4)
   else buildcodetree(a, @(pushconst.a, identity, f, arithseq((j - i + 2)/ 2, 2, i)), j + 2)
  else if a_i in"PARA LOCAL"
  then buildcodetree(a, push(f, tree.cnode(a_i, a_(i + 1), 0)), i + 2)
  else if a_i in"CALL"
  then let noargs = toint(a_(i + 1))
   let c = cnode(a_i, a_(i + 2), 0)
   buildcodetree(a, push(pop(f, noargs), tree(c, top(f, noargs))), i + 3)
  else if a_i ="SET"_1 
  then let c = cnode(a_i, a_(i + 1), 2)
   buildcodetree(a, push(pop(f, 2), tree(c, top(f, 2))), i + 2)
  else if a_i ="FLD"_1 
  then let args = top(f, 2)
   let tr = if a_(i + 1)="1"_1 
    then tree(cnode("IDXUC"_1,"0"_1, 2), args)
    else // 8 is number of bytes in word // 
    tree(cnode("ADD"_1,"0"_1, 2), [ args_1, tree.cnode("LIT"_1, toword(toint.arg.label(args_2)* 8), 0)])
   buildcodetree(a, push(pop(f, 2), tr), i + 2)
  else if a_i ="FLAT"_1 
  then if a_(i + 1)="1"_1 
   then buildcodetree(a, f, i + 2)
   else buildcodetree(a, push(pop.f, tree(cnode(a_i, a_(i + 1), 0), [ top.f])), i + 2)
  else if a_i in"$build $wordlist"
  then let noelements = toint(a_(i + 1))
   let prefix = [ tree.cnode("LIT"_1,"0"_1, 0), tree.cnode("LIT"_1, a_(i + 1), 0)]
   let c = cnode("RECORD"_1,"0"_1)
   buildcodetree(a, push(pop(f, noelements), tree(c, prefix + top(f, noelements))), i + 2)
  else if a_i ="RECORDS"_1 
  then // last element in record becomes the first // 
   let noelements = toint(a_(i + 1))
   let c = cnode("RECORD"_1,"0"_1)
   buildcodetree(a, push(pop(f, noelements), tree(c, [ top.f]+ top(pop.f, noelements - 1))), i + 2)
  else let noargs = toint(a_(i + 1))
  let c = cnode(a_i,"0"_1)
  assert not(a_i ="if"_1)∨ noargs = 3 report"Incorrect number of args on if"
  buildcodetree(a, push(pop(f, noargs), tree(c, top(f, noargs))), i + 2)

Function removeflat(f:func)func replacecodetree(f, removeflat.codetree.f)

Function removeflat(t:tree.cnode)tree.cnode 
 if nosons.t = 0 then t else tree(label.t, @(addflat, removeflat, empty:seq.tree.cnode, sons.t))

function addflat(s:seq.tree.cnode, t:tree.cnode)seq.tree.cnode 
 if inst.label.t ="FLAT"_1 
  then let firstson = t_1 
   s + @(+, fixup2.firstson, empty:seq.tree.cnode, arithseq(toint.arg.label.t, 1, 0))
  else s + t

function fixup2(x:tree.cnode, i:int)tree.cnode 
 tree(cnode("IDXUC"_1,"0"_1, 2), [ x, tree.cnode("LIT"_1, toword.i, 0)])

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

Function print(t:tree.cnode)seq.word 
 let inst = inst.label.t 
  @(+, print,"", sons.t)+ if inst in"PARA LIT CONST LOCAL FREF WORD FLAT"
   then [ inst, arg.label.t]
   else if inst in"CALL CALLB"
   then [ inst, toword.nosons.t, arg.label.t]
   else if inst ="SET"_1 then [ inst, arg.label.t]else [ inst, toword.nosons.t]

Function print(a:func)seq.word 
 {"<"+ number.a + number.a + symboltext.a +">"+ print.codetree.a }

function cnode(a:word, b:word, int)cnode cnode(a, b)

Function cnode(a:word, b:word)cnode export

Function in(l:seq.word, t:tree.cnode)boolean 
 if inst.label.t in l then true else @(∨, in.l, false, sons.t)

--------

type ch1result is record nodecount:int, para:int

function ch1(t:tree.cnode, a:ch1result, son:int)ch1result 
 if nodecount.a > 30 
  then a 
  else if son ≤ nosons.t 
  then ch1(t, ch1(t_son, a, 1), son + 1)
  else if inst.label.t ="PARA"_1 
  then if arg.label.t = toword.para.a 
   then ch1result(nodecount.a + 1, para.a - 1)
   else ch1result(nodecount.a + 1, -1)
  else if inst.label.t in"CALL NOINLINE FREF"
  then ch1result(nodecount.a + 1, -1)
  else ch1result(nodecount.a + 1, para.a)

Function simple(s:func)boolean 
 // Check to see if simple inline expansion is possible for function. All parameters must occur exactly once in order without any function occuring before the last parameter that may cause a side-effect making the order of evaluation important. It also must be short.// 
  let a = ch1(codetree.s, ch1result(0, nopara.s), 1)
  nodecount.a < 30 ∧ para.a = 0

_____________________

Converting func to lib symbol. Must remove CONST and FREF and CALL instructions. Conversion would be simpler if constants had RECORD as suffix instead of prefix.

In the libsym, if the inst field begins with"USECALL"then the rest of inst the intermediate representation. Otherwise the inst is the code that should be added after the parameters. For example ;"USECALL PARA 2 PARA 1 ADD 2"and"ADD 2"are equivalent representations of a function.

function tolibsyminst(cmap:seq.seq.word, lib:word, a:func)seq.word 
 let y = if number.a in"seqZTzseqZintZT pseqZTzseqZintZTzseqZTzseq dseqZTzseqZintZTZTzseq fastsubseqZTzseqZintZTzseqZint cseqZTzseqZintZT blockseqZTzblockseqZintZintZTzseqzseq arithmeticseqZTzarithmeticseqZintZTZT"
   then"ALWAYSCALL"
   else if simple.a 
   then let nopara = nopara.a 
    let x = expandconst(cmap, print.codetree.a, 1,"")
    if length.x > 100 
    then"ALWAYSCALL"
    else let verysimple = nopara = 0 ∨ nopara = 1 ∧ subseq(x, 1, 2)="PARA 1"∨ nopara = 2 ∧ subseq(x, 1, 4)="PARA 2 PARA 1"∨ nopara = 3 ∧ subseq(x, 1, 6)="PARA 3 PARA 2 PARA 1"∨ nopara = 4 ∧ subseq(x, 1, 8)="PARA 4 PARA 3 PARA 2 PARA 1"
    if verysimple ∧ not("PARA"_1 in subseq(x, nopara * 2 + 1, length.x))∧ not("SET"_1 in x)
    then subseq(x, nopara * 2 + 1, length.x)
    else"USECALL"+ x 
   else"ALWAYSCALL"
  if y ="ALWAYSCALL"
  then if"STATE"in codetree.a 
   then [ number.a, toword.nopara.a,"STATE"_1,"1"_1]
   else [ number.a, toword.nopara.a]
  else y

function expandconst(cmap:seq.seq.word, s:seq.word, i:int, result:seq.word)seq.word 
 if length.result > 100 ∧ length.cmap > 0 
  then result 
  else if i + 1 > length.s 
  then assert i - 1 = length.s report"premature end"+ toword.i + toword.length.s + s 
   result 
  else if s_i in"CALL CALLB"
  then expandconst(cmap, s, i + 3, result + s_i + s_(i + 1)+ s_(i + 2))
  else if s_i ="CONST"_1 
  then let c = cmap_toint(s_(i + 1))
   let expanded = if c_1 ="RECORD"_1 
    then expandconst(cmap, c, 3,"")+ [ c_1, c_2]
    else expandconst(cmap, c, 1,"")
   expandconst(cmap, s, i + 2, result + expanded)
  else expandconst(cmap, s, i + 2, result + [ s_i]+ s_(i + 1))

function isdigits(w:word)boolean @(∧, isdigit, true, decode.w)

function isdigit(i:int)boolean between(i, 48, 57)

Function tolibsym(constmapping:seq.seq.word, lib:word, f:func)libsym 
 let p = libsym(mytype.symboltext.f, number.f, tolibsyminst(constmapping, lib, f))
  p

