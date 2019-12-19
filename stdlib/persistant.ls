Module persistant

use bits

use blockseq.flddesc

use deepcopy.linklists2

use fileio

use internalbc

use ipair.linklists2

use libscope

use llvm

use packedseq.flddesc

use packedseq.seq.flddesc

use persistantseq.libmod

use persistantseq.libsym

use persistantseq.mytype

use reconstruct

use seq.const3


use seq.flddesc

use seq.int

use seq.liblib

use seq.libmod

use seq.libsym

use seq.linklists2

use seq.mytype

use seq.seq.flddesc

use seq.tree.seq.word

use seq.word

use seq.word3

use stack.tree.seq.word

use stdlib

use tree.seq.word


type word3encoding is encoding word3

Function wordcount int length.orderadded.word3encoding

Function worddata seq.int 
 let ws = orderadded.word3encoding 
  @(+, eword, [ C64.0, C64.length.ws], ws)

_________________

encode Functions

The linklists2 type contains a seq of integers that represents the memory.Any memory locations that store the type word are linked into a linked list begining with wordthread. Two values are packed into the integer is store in the seq. One is the word3 encoding and the other the next value in the linked list. Any memory locations that store an address of another memory are linked into a linked list beginning with offsetthread. In this case the element in the seq is represents two interger values. One is the next value in the linked list and the other is the index of the refrenced memory location.

Function a(linklists2)seq.int export

Function wordthread(linklists2)int export

Function offsetthread(linklists2)int export

Function wordseqthread(linklists2)int export

Function linklists2(a:seq.int, wordthread:int, offsetthread:int, wordseqthread:int)linklists2 export

Function initializer(conststypex:llvmtype, data:linklists2)int 
assert wordthread.data=0 &and wordseqthread.data=0 report "wordthread or data thread is not zero"
 C(conststypex, [ AGGREGATE, 
 C64.0, 
 C64(length.a.data + 3), 
 C64.wordthread.data, 
 C64.offsetthread.data, 
 C64.wordseqthread.data]+ a.data)+ 1

type word3 is record toword:word, index:int

function word3(a:word) word3 word3( a,0)

function addindex(e:word3,i:int) word3 word3(toword.e,i)

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

Function place(a:linklists2)int length.a.a + 4

Function word33(a:word)int findindex(word3.a, word3encoding)

function eword(w:word3)seq.int 
 let a = decode.toword.w 
  @(+, C64, [ C64.0, C64.length.a], a)

function cast2int(liblib)int builtin.NOOP

Function cast2intseq(int)seq.int builtin.NOOP

Function cast2word(int)word builtin.NOOP

type trackflds is record l:linklists2, flds:seq.flddesc, state:int

type flddesc is record index:int, kind:word

function flddesc(int, word)flddesc export

type const3 is record place:int, flds:seq.flddesc

function =(a:flddesc, b:flddesc)boolean index.a = index.b ∧ kind.a = kind.b

type const3e is encoding const3

Function trackflds(l:linklists2, flds:seq.flddesc, state:int)trackflds export

Function l(trackflds)linklists2 export

Function flds(trackflds)seq.flddesc export

Function state(trackflds)int export

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
  else if c_1 ="WORDS"_1 
  then let len = toint(c_2)
   // assert false report subseq(s, i, len + 1)// 
   buildconsttree(s, i + len + 2, push(result, tree.subseq(s, i, i + len + 1)))
  else buildconsttree(s, i + 2, push(result, tree.c))

function addconst(l:linklists2, t:tree.seq.word)ipair.linklists2 
 // First build description of record. This may add other const records to l // 
  let y = @(getindex, identity, trackflds(l, empty:seq.flddesc, 1), sons.t)
  // look up CRECORD to see if we have already used it. // 
  let x = decode(encode(const3(place.l.y, flds.y), const3e), const3e)
  if place.x ≠ place.l.y 
  then ipair(place.x, l.y)
  else // have seen this CRECORD before so process it // 
   let  newlist=@(buildtheobject.place.l.y, identity, l.y, flds.x)
  ipair(place.l.y, newlist)

function getindex(f:trackflds, t:tree.seq.word)trackflds 
 let typ = label(t)_1 
  if typ ="LIT"_1 
  then trackflds(l.f, flds.f + flddesc(C64.toint(label(t)_2),"LIT"_1), if state.f = 1 ∧ label.t ="LIT 0"
   then 2 
   else if state.f = 2 then 3 else 0)
  else if typ ="WORD"_1 
  then let discard=word33(label(t)_2)
    trackflds(l.f, flds.f + flddesc(C64.hash(label(t)_2),"LIT"_1), if state.f = 3 then 3 else 0)
  else if typ ="WORDS"_1 
  then // assert false report"in get index"+ subseq(label.t, 3, length.label.t)// 
   let k = addwordseq(l.f, subseq(label.t, 3, length.label.t))
   trackflds(value.k, flds.f + flddesc(index.k,"CRECORD"_1), 0)
  else if typ ="FREF"_1 
  then trackflds(l.f, flds.f + flddesc(C(i64, [ CONSTCECAST, 9, typ.ptr.getftype(label(t)_2), C.[ label(t)_2]]),"LIT"_1), 0)
  else assert label(t)_1 ="CRECORD"_1 report"PROBLEM"
  let k = addconst(l.f, t)
  trackflds(value.k, flds.f + flddesc(index.k,"CRECORD"_1), 0)

Function buildtheobject(objectstart:int, l:linklists2, d:flddesc)linklists2 
 FORCEINLINE.let typ = kind.d 
 assert typ &ne "WORD"_1 report "no longer expection word"
  let newoffsetthread = if typ ="CRECORD"_1 then place.l else offsetthread.l 
  linklists2(a.l + if typ ="LIT"_1 
   then index.d 
   else if typ ="WORD"_1 
   then C64.packit(wordthread.l, index.d)
   else C64.packit(offsetthread.l, index.d), if typ ="WORD"_1 then place.l else wordthread.l, newoffsetthread, wordseqthread.l)

type trackele is record l:linklists2, places:seq.int

function l(trackele)linklists2 export

function places(trackele)seq.int export

function trackele(l:linklists2, places:seq.int)trackele export

function addrecord(l:linklists2, s:mytype)ipair.linklists2 addwordseq(l, towords.s)

Function addoffset(l:linklists2, index:int)linklists2 
 linklists2(a.l + C64.packit(offsetthread.l, index), wordthread.l, place.l, wordseqthread.l)

function addrecord(l1:linklists2, sym:libsym)ipair.linklists2 
 let a = addwordseq(l1, returntype.sym)
  let b = addwordseq(value.a, instruction.sym)
  let l = value.b 
  ipair(place.l, l + fsig.sym + a + b)

Function addliblib(lin:linklists2, t:liblib)ipair.linklists2 
 let a = addwordseq(lin, libname.t)
  let c = addseq(value.a, mods.t)
  let l = value.c 
  let l5 = l + a + 0 + c + timestamp.t + toint.readonly.t 
  ipair(place.l, l5)

function addrecord(lin:linklists2, modx:libmod)ipair.linklists2 
 let a = addseq(lin, defines.modx)
  let b = addseq(value.a, exports.modx)
  let l = value.b 
  let l5 = l + toint.parameterized.modx + modname.modx + a + b 
  ipair(place.l, l5)

Function +(l:linklists2, i:int)linklists2 linklists2(a.l + C64.i, wordthread.l, offsetthread.l, wordseqthread.l)

Function +(l:linklists2, w:word)linklists2 
  let discard=word33.w
     l+hash.w 
     
 
Function +(l:linklists2, b:ipair.linklists2)linklists2 
 linklists2(a.l + C64.packit(offsetthread.l, index.b), wordthread.l, place.l, wordseqthread.l)

Function addwordseq(t:linklists2, a:seq.word)ipair.linklists2
  let discard= @(+,word33,0,a)
   addintseq(t,  @(+,    hash,empty:seq.int,a)) 

Function addintseq(t:linklists2, s:seq.int)ipair.linklists2 
 ipair(place.t, linklists2(a.t + @(+, C64, [ C64.0, C64.length.s], s), wordthread.t, offsetthread.t, wordseqthread.t))


function cast2int(s:seq.int)int builtin.NOOP

______________________________

