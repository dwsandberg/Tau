module buildtree


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

Function cnode(a:word, b:word)cnode export


Function =(a:cnode, b:cnode)boolean inst.a = inst.b ∧ 
 if inst.a in "SET FLAT FLD LIT LOCAL FREF PARA WORD" then arg.b = arg.a else true

type func is record nopara:int, returntype:mytype, mangledname:word, codetree:tree.cnode, flags:seq.word


Function dummyfunc func 
 func(0,mytype."int","dummyfunc"_1, buildcodetree("X LIT 1"),"noprofile")

Function func(nopara:int, returntype:mytype, mangledname:word, codetree:tree.cnode, flags:seq.word)func 
 export

Function returntype(f:func) mytype export

Function nopara(func)int export

Function mangledname(s:func)word  export

Function flags(s:func)seq.word export

Function codetree(f:func)tree.cnode export

Function replacecodetree(f:func, new:tree.cnode)func 
 func(nopara.f, returntype.f, mangledname.f, new, flags.f)

function =(a:func, b:func)boolean mangledname.a = mangledname.b

type bld is record state:int,last:word,stk:stack.tree.cnode 

use seq.bld

use seq.word


function  addinstruction(b:bld,w:word) bld
// state :0  initial ,1  found CALL, 2 at noargs, 4 at funcname in CALL //
OPTIONS("FORCEINLINE",
  let newstk=if state.b < 2  &or ( last.b ="FLAT"_1 &and w="1"_1 )  then
    stk.b else 
    assert  last.b &ne "RECORDS"_1 report "X"
    let z = if last.b in " LIT LOCAL FREF PARA WORD" then 
           tree.cnode(last.b,w) 
           else if last.b in "FLD" then
            tree(if w="1"_1 then cnode("IDXUC"_1,"0"_1) else cnode( "getaddressZbuiltinZTzseqZint"_1,"0"_1), top(stk.b, 2))
          else  if last.b in "SET" then    tree(cnode(last.b,w),top(stk.b,2))
          else if  last.b in"$build $wordlist"
              then let noelements = toint(w)
                   let prefix = [ tree.cnode("LIT"_1,"0"_1), tree.cnode("LIT"_1, w)]
            tree(cnode("RECORD"_1,"0"_1), prefix + removeflat(top(stk.b, noelements)))
             else if last.b="RECORDS"_1 
  then // last element in record becomes the first // 
    tree(cnode("RECORD"_1,"0"_1), removeflat([ top.stk.b]+ top(pop.stk.b, toint(w) - 1)))
          else  if last.b ="FLAT"_1 
          then   tree(cnode(last.b, w), [ top.stk.b])
          else  
            let sons = top( stk.b, toint(if state.b=4 then  last.b else w))
           tree(cnode( if state.b=4 then w else last.b,if state.b=4 then last.b else w),   
            if last.b = "RECORD"_1 then          removeflat.sons else sons )
     push(pop(stk.b, if last.b in "$build $wordlist RECORD RECORDS" then toint(w) else  nosons.z),z)
  bld(  if state.b=0 then if w="CALL"_1 then 1 else 2  
        else if state.b=1 then 4 else 0 ,  w , newstk))
 
Function buildcodetree(data:seq.word) tree.cnode OPTIONS("special",top.stk.@(addinstruction,identity,bld(0,"START"_1,empty:stack.tree.cnode),
subseq(data,2,length.data)))
 

Function oldbuildcodetree(a:seq.word)tree.cnode 
 // let b = check(a, 0, 1,"") //
  buildcodetree(a, empty:stack.tree.cnode, 2)


function buildcodetree(a:seq.word, f:stack.tree.cnode, i:int)tree.cnode 
 if i > length.a 
  then top.f 
  else if a_i in"LIT  WORD FREF PARA LOCAL"
  then buildcodetree(a, push(f, tree.cnode(a_i, a_(i + 1))), i + 2)
  else if a_i in"CALL"
  then let noargs = toint(a_(i + 1))
   let c =//  cnode(a_i, a_(i + 2)) // cnode(a_(i + 2),"0"_1)
   buildcodetree(a, push(pop(f, noargs), tree(c, top(f, noargs))), i + 3)
  else if a_i ="SET"_1 
  then let c = cnode(a_i, a_(i + 1))
   buildcodetree(a, push(pop(f, 2), tree(c, top(f, 2))), i + 2)
  else if a_i ="FLD"_1 
  then let args = top(f, 2)
   let tr =   tree(if a_(i + 1)="1"_1 then cnode("IDXUC"_1,"0"_1) else cnode( "getaddressZbuiltinZTzseqZint"_1,"0"_1), args)
   buildcodetree(a, push(pop(f, 2), tr), i + 2)
  else if a_i ="FLAT"_1 
  then if a_(i + 1)="1"_1 
   then buildcodetree(a, f, i + 2)
   else 
    buildcodetree(a, push(pop.f, tree(cnode( a_i, a_(i + 1)), [ top.f])), i + 2)
    else if a_i in"$build $wordlist"
  then let noelements = toint(a_(i + 1))
   let prefix = [ tree.cnode("LIT"_1,"0"_1), tree.cnode("LIT"_1, a_(i + 1))]
   let c = cnode("RECORD"_1,"0"_1)
   buildcodetree(a, push(pop(f, noelements), tree(c, prefix + removeflat(top(f, noelements)))), i + 2)
  else if a_i ="RECORDS"_1 
  then // last element in record becomes the first // 
   let noelements = toint(a_(i + 1))
   let c = cnode("RECORD"_1,"0"_1)
   buildcodetree(a, push(pop(f, noelements), tree(c, removeflat([ top.f]+ top(pop.f, noelements - 1)))), i + 2)
  else let noargs = toint(a_(i + 1))
  let c = cnode(a_i,"0"_1)
  // assert not(a_i ="if"_1)∨ noargs = 3 report"Incorrect number of args on if" //
  let sons=if inst.c="RECORD"_1 then removeflat.top(f, noargs) else top(f, noargs)
  buildcodetree(a, push(pop(f, noargs), tree(c, sons)), i + 2)
  
function removeflat(s:seq.tree.cnode) seq.tree.cnode
 @(+,processson,empty:seq.tree.cnode,s)

function processson(t:tree.cnode) seq.tree.cnode
     if inst.label.t="FLAT"_1  then
       let firstson = t_1 
       @(+, fixup2.firstson, empty:seq.tree.cnode, arithseq(toint.arg.label.t, 1, 0))
       else [t]
       

function fixup2(x:tree.cnode, i:int)tree.cnode 
 tree(cnode("IDXUC"_1,"0"_1), [ x, tree.cnode("LIT"_1, toword.i)])


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


Function print(t:tree.cnode)seq.word 
 let inst = inst.label.t 
  @(+, print,"", sons.t)+ if inst in"PARA LIT LOCAL FREF WORD FLAT"
   then [ inst, arg.label.t]
   else if inst in"CALLB"
   then [ inst, toword.nosons.t, arg.label.t]
   else if inst ="SET"_1 then [ inst, arg.label.t]else [ inst, toword.nosons.t]

Function print(a:func)seq.word 
 {"<"+ mangledname.a +  towords.returntype.a +">"+ print.codetree.a }



Function in(l:seq.word, t:tree.cnode)boolean 
 if inst.label.t in l then true else @(∨, in.l, false, sons.t)

--------

type ch1result is record nodecount:int, para:seq.word

use seq.ch1result

function +(a:ch1result,t:tree.cnode)  ch1result 
if nodecount.a > 15 then  ch1result(1000,"fail") else
let b = ch1(t)
ch1result(nodecount.a+nodecount.b,para.a+para.b)

function ch1(t:tree.cnode)ch1result 
   if inst.label.t ="PARA"_1 then ch1result(1,[arg.label.t])
  else  if inst.label.t  in "NOINLINE LOOP STATE" then ch1result(1000,"fail")
   else @(+,identity,ch1result(1,   ""),sons.t)
   
Function functype(t:tree.cnode,nopara:int) word
  let a = ch1(t)
   if nodecount.a > 15 &or "fail"_1 in para.a then "COMPLEX"_1
   else  if para.a = @(+,toword,"",arithseq(nopara,-1,nopara)) then "SIMPLE"_1
   else "INLINE"_1


_____________________


Function tolibsym( lib:word, a:func)libsym 
 // Converting func to lib symbol.
 In the libsym, if the inst field begins with"USECALL"then the rest of inst the intermediate representation. Otherwise the inst is the code that should be added after the parameters. For example ;"USECALL PARA 2 PARA 1 ADD 2"and"ADD 2"are equivalent representations of a function.
 //
  let inst = if inst.label.codetree.a ="STATE"_1 then
    [ mangledname.a, toword.nopara.a]
else  if ("SIMPLE"_1 in flags.a )
   then 
      let nopara = nopara.a 
    let x = print.codetree.a
    let verysimple = nopara = 0 ∨ nopara = 1 ∧ subseq(x, 1, 2)="PARA 1"∨ nopara = 2 ∧ subseq(x, 1, 4)="PARA 2 PARA 1"∨ nopara = 3 ∧ subseq(x, 1, 6)="PARA 3 PARA 2 PARA 1"∨ nopara = 4 ∧ subseq(x, 1, 8)="PARA 4 PARA 3 PARA 2 PARA 1"
    if verysimple ∧ not("PARA"_1 in subseq(x, nopara * 2 + 1, length.x))∧ not("SET"_1 in x)
    then subseq(x, nopara * 2 + 1, length.x)
    else"USECALL"+ x 
   else 
   [ mangledname.a, toword.nopara.a]
libsym(returntype.a, mangledname.a, inst)



 

