module persistantseq.T

use stdlib

use seq.T

use persistant

use ipair.linklists2

 function       addele(t:trackele,s:T) trackele  
    let a = addrecord(l.t,s)
    trackele(value.a,places.t+index.a)
    
 function addrecord(linklists2,s:T) ipair.linklists2 unbound
 
 Function addseq(l:linklists2,s:seq.T) ipair.linklists2
    let x =@(addele,identity,trackele(l,empty:seq.int),s)
    let t = linklists2(a.l.x + C64.0 + C64.length.s, wordthread.l.x, offsetthread.l.x, wordseqthread.l.x)
    ipair(place.l.x,@(addoffset,identity,t,places.x) )


function identityf(s:seq.T)seq.T s

use process.seq.T


 use llvm
 
 use fileio
 
 use process.seq.word
 
 Function flush(s:erecord.T)seq.word 
 if ispersistant.s 
  then   
    let p=process.createlib2(s)
    result.p
  else"Encoding is not persistant."


use seq.libtype

use set.libtype

use libscope

use reconstruct

use internalbc

Function createlib2(s:erecord.T) seq.word 
  let thedata = result.process.identityf.mapping.s 
  let libname=merge("Q"+ name.s)
   let symtab ="libname initlib5 words wordlist list init22"
  let discard = @(+, C, 0, symtab)
  let data1=  addseq(createlinkedlists,thedata )  
  let liblib = addliblib( value.data1, emptyliblib.libname)
  let data = value.liblib 
  let words = worddata 
  let worddatatype = array(length.words + 2, i64)
  let wordstype = array(2 + wordcount, i64)
  let conststype2 = array(length.a.data + 5, i64)
  let libnametype = array(length.decode.libname + 1, i8)
  let libnameptr = C(ptr.i8, [ CONSTGEP, typ.libnametype, typ.ptr.libnametype, C."libname", typ.i32, C32.0, typ.i32, C32.0])
  let deflist = [ // libname // 
   [ MODULECODEGLOBALVAR, 
   typ.libnametype, 
   2, 
   C(libnametype, [ CONSTDATA]+ decode.libname + 0)+ 1, 
   3, 
   align4, 
   0], 
  [ MODULECODEFUNCTION, 
  typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64, ptr.i64, ptr.i64], 
  0, 
  1, 
  0, 
  1, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0], 
  [ MODULECODEGLOBALVAR, typ.wordstype, 2, C(i64, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  [ MODULECODEGLOBALVAR, 
  typ.worddatatype, 
  2, 
  1 + C(worddatatype, [ AGGREGATE, C64.0, C64.length.words]+ words), 
  3, 
  align8 + 1, 
  0], 
  [ MODULECODEGLOBALVAR, 
  typ.conststype2, 
  2, 
  C(conststype2, [ AGGREGATE, 
  C64.0, 
  C64(length.a.data + 3), 
  C64.wordthread.data, 
  C64.offsetthread.data, 
  C64.wordseqthread.data]+ a.data)+ 1, 
  3, 
  align8 + 1, 
  0], 
  // init22 // [ MODULECODEFUNCTION, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
  let bodytxts = [ BLOCKCOUNT(1, 1)+ CALL(1, 0, 32768, typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64, ptr.i64, ptr.i64], C."initlib5", libnameptr, getelementptr(wordstype,"words", 0), getelementptr(worddatatype,"wordlist", 0), getelementptr(conststype2,"list", 0), getelementptr(conststype2,"list", index.liblib + 1), getelementptr(conststype2,"list", index.data1 + 1))+ RET.3]
  let b=createlib(llvm(deflist, bodytxts, typerecords), libname,"")
  "OK"


module persistant

use deepcopy.linklists2

use bits

use fileio

use internalbc

use ipair.linklists2

use libscope

use llvm

use seq.const3

use seq.encoding.llvmtype

use seq.flddesc

use seq.int

use seq.liblib

use seq.libmod

use seq.libsym


use seq.linklists2

use seq.mytype

use seq.tree.seq.word

use seq.word3

use stack.tree.seq.word

use stdlib

use tree.seq.word

use reconstruct

type word3encoding is encoding word3

Function wordcount int length.mapping.word3encoding

Function worddata seq.int 
 let ws = mapping.word3encoding 
  @(+, eword, [ C64.0, C64.length.ws], ws)

_________________

encode Functions

The linklists2 type contains a seq of integers that represents the memory.Any memory locations that store the type word are linked into a linked list begining with wordthread. Two values are packed into the integer is store in the seq. One is the word3 encoding and the other the next value in the linked list. Any memory locations that store an address of another memory are linked into a linked list beginning with offsetthread. In this case the element in the seq is represents two interger values. One is the next value in the linked list and the other is the index of the refrenced memory location.


Function a(linklists2)seq.int export

Function wordthread(linklists2)int export

Function offsetthread(linklists2)int export

Function wordseqthread(linklists2)int export

Function linklists2(a:seq.int, wordthread:int, offsetthread:int, wordseqthread:int) linklists2 export

Function initializer(conststypex:encoding.llvmtype, data:linklists2)int 
 C(conststypex, [ AGGREGATE, 
 C64.0, 
 C64(length.a.data + 3), 
 C64.wordthread.data, 
 C64.offsetthread.data, 
 C64.wordseqthread.data]+ a.data)+ 1

type word3 is record toword:word

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

Function place(a:linklists2)int length.a.a + 4

Function word33(a:word)int encoding.encode(word3.a, word3encoding)

function eword(w:word3)seq.int 
 let a = decode.toword.w 
  @(+, C64, [ C64.0, C64.length.a], a)




function cast2int(liblib)int builtin.NOOP

Function cast2intseq(int)seq.int builtin.NOOP

Function cast2word(int)word builtin.NOOP


type trackflds is record l:linklists2, flds:seq.flddesc, state:int

type flddesc is record index:int, kind:word

function flddesc(int,word) flddesc export

type const3 is record place:int, flds:seq.flddesc

function =(a:flddesc, b:flddesc)boolean index.a = index.b ∧ kind.a = kind.b

type const3e is encoding const3

Function trackflds(l:linklists2, flds:seq.flddesc, state:int) trackflds export

Function  l(trackflds) linklists2 export

Function  flds(trackflds) seq.flddesc export

Function state(trackflds) int export


use blockseq.flddesc

use packedseq.flddesc

use seq.seq.flddesc

use packedseq.seq.flddesc


function =(a:const3, b:const3)boolean flds.a = flds.b

function hash(a:const3)int length.flds.a + @(+, index, 0, flds.a)

Function addconst(l:linklists2, fullinst:seq.word)ipair.linklists2 
 addconst(l, buildconsttree(fullinst, 2, empty:stack.tree.seq.word))

function buildconsttree(s:seq.word, i:int, result:stack.tree.seq.word)tree.seq.word 
 if i + 1 > length.s 
  then top.result 
  else let c = subseq(s, i, i + 1)
  if c_1 ="CRECORD"_1 
  then let nosons = toint(c_2)
   buildconsttree(s, i + 2, push(pop(result, nosons), tree(c, top(result, nosons))))
  else if c_1="WORDS"_1 then
          let len=toint.c_2
    // assert false report subseq(s,i,len+1) //
    buildconsttree(s, i + len+2, push(result, tree.subseq(s,i,i+len+1)))
  else buildconsttree(s, i + 2, push(result, tree.c))

function addconst(l:linklists2, t:tree.seq.word)ipair.linklists2 
 // First build description of record. This may add other const records to l // 
  let y = @(getindex, identity, trackflds(l, empty:seq.flddesc, 1), sons.t)
  // look up CRECORD to see if we have already used it. // 
  let x = decode(encode(const3(place.l.y, flds.y), const3e), const3e)
  if place.x ≠ place.l.y 
  then ipair(place.x, l.y)
  else // have seen this CRECORD before so process it // 
  // assert not(nosons.t > 4 ∧ state.y = 3)∨ isnumber.(label.t_1)_2 report"ZZZ"+ @(+, label,"", sons.t)+ label.t // 
  let newlist = if nosons.t > 4 ∧ state.y = 3 ∧ toint(label(t_1)_2)= nosons.t - 2 
   then // word seq // 
    linklists2(@(+, index, a.l.y + C64.wordseqthread.l.y, subseq(flds.y, 2, length.flds.y)), wordthread.l.y, offsetthread.l.y, place.l.y)
   else @(buildtheobject.place.l.y, identity, l.y, flds.x)
  ipair(place.l.y, newlist)

function getindex(f:trackflds, t:tree.seq.word)trackflds 
 let typ = label(t)_1 
  if typ ="LIT"_1 
  then trackflds(l.f, flds.f + flddesc(C64.toint(label(t)_2),"LIT"_1), if state.f = 1 ∧ label.t ="LIT 0"
   then 2 
   else if state.f = 2 then 3 else 0)
  else if typ ="WORD"_1 
  then trackflds(l.f, flds.f + flddesc(word33(label(t)_2),"WORD"_1), if state.f = 3 then 3 else 0)
  else if typ="WORDS"_1 then
   // assert false report "in get index" + subseq(label.t,3,length.label.t) //
   let k = addwordseq(l.f, subseq(label.t,3,length.label.t))
    trackflds(value.k, flds.f + flddesc(index.k,"CRECORD"_1), 0) 
  else if typ ="FREF"_1 
  then trackflds(l.f, flds.f + flddesc(C(i64, [ CONSTCECAST, 9, typ.ptr.getftype(label(t)_2), C.[ label(t)_2]]),"LIT"_1), 0)
  else assert label(t)_1 ="CRECORD"_1 report"PROBLEM"
  let k = addconst(l.f, t)
  trackflds(value.k, flds.f + flddesc(index.k,"CRECORD"_1), 0)

Function buildtheobject(objectstart:int, l:linklists2, d:flddesc)linklists2 
 FORCEINLINE.let typ = kind.d 
  let newwordthread = if typ ="WORD"_1 then place.l else wordthread.l 
  let newoffsetthread = if typ ="CRECORD"_1 then place.l else offsetthread.l 
  linklists2(a.l + if typ ="LIT"_1 
   then index.d 
   else if typ ="WORD"_1 
   then C64.packit(wordthread.l, index.d)
   else C64.packit(offsetthread.l, index.d), newwordthread, newoffsetthread, wordseqthread.l)
   

type   trackele is record l:linklists2,places:seq.int

function l(trackele) linklists2 export

function places(trackele) seq.int export

function  trackele(l:linklists2,places:seq.int) trackele export


function addrecord(l:linklists2,s:mytype) ipair.linklists2
    addwordseq(l,towords.s)

Function addoffset(l:linklists2,index:int) linklists2
linklists2(a.l+C64.packit(offsetthread.l, index),wordthread.l,place.l,wordseqthread.l)
  
function addrecord(l1:linklists2,sym:libsym) ipair.linklists2
    let a = addwordseq(l1,returntype.sym)
   let b =addwordseq(value.a,instruction.sym)
   let l=value.b
    ipair(place.l,l+fsig.sym+a+b )
   
Function addliblib(lin:linklists2,t:liblib) ipair.linklists2
   let a = addwordseq(lin,libname.t)
   let c =addseq(value.a,mods.t)
   let l=value.c
   let l5=l+a+0+c+timestamp.t+toint.readonly.t 
   ipair(place.l,l5)

use seq.word

use persistantseq.libsym

use persistantseq.mytype

use persistantseq.libmod

function addrecord(lin:linklists2,modx:libmod) ipair.linklists2
   let a = addseq(lin,defines.modx)
   let b =addseq(value.a,exports.modx)
   let l=value.b
     let l5=l+toint.parameterized.modx+modname.modx+a+b   
   ipair(place.l,l5)

Function +(l:linklists2,i:int) linklists2 
   linklists2(a.l+C64.i,wordthread.l,offsetthread.l,wordseqthread.l)   

Function +(l:linklists2,w:word) linklists2 
   linklists2(a.l+C64.packit(wordthread.l,word33.w),place.l,offsetthread.l,wordseqthread.l)   

Function +(l:linklists2,b:ipair.linklists2) linklists2 
  linklists2(a.l+C64.packit(offsetthread.l, index.b),wordthread.l,place.l,wordseqthread.l)
 
Function addwordseq(t:linklists2, a:seq.word) ipair.linklists2
ipair(place.t, linklists2(a.t + @(+, C64word33, [ C64.wordseqthread.t, C64.length.a], a), wordthread.t, offsetthread.t, place.t))

function C64word33(a:word)int C64.word33.a

function cast2int(s:seq.int)int builtin.NOOP

______________________________

