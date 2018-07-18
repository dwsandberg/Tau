module persistant

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

use seq.libtype

use seq.linklists2

use seq.mytype

use seq.tree.seq.word

use seq.word3

use stack.tree.seq.word

use stdlib

use tree.seq.word

type word3encoding is encoding word3

Function wordcount int length.mapping.word3encoding

Function worddata seq.int 
 let ws = mapping.word3encoding 
  @(+, eword, [ C64.0, C64.length.ws], ws)

_________________

encode Functions

The linklists2 type contains a seq of integers that represents the memory.Any memory locations that store the type word are linked into a linked list begining with wordthread. Two values are packed into the integer is store in the seq. One is the word3 encoding and the other the next value in the linked list. Any memory locations that store an address of another memory are linked into a linked list beginning with offsetthread. In this case the element in the seq is represents two interger values. One is the next value in the linked list and the other is the index of the refrenced memory location.

type linklists2 is record a:seq.int, wordthread:int, offsetthread:int, wordseqthread:int

Function createlinkedlists linklists2 linklists2(empty:seq.int, 0, 0, 0)

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

Function getftype(w:word)encoding.llvmtype 
 let a = @(+, count.90, 1, decode.w)
  function.constantseq(a, i64)

function count(val:int, i:int)int if val = i then 1 else 0

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

function       addele(t:trackele,s:libsym) trackele
    let a = addlibsym(l.t,s)
    trackele(value.a,places.t+index.a)

function       addele(t:trackele,s:libmod) trackele
    let a = addlibmod(l.t,s)
    trackele(value.a,places.t+index.a)
    
function       addele(t:trackele,s:libtype) trackele
    let a = addlibtype(l.t,s)
    trackele(value.a,places.t+index.a)
    
function       addele(t:trackele,s:mytype) trackele
    let a = addwordseq(l.t,towords.s)
    trackele(value.a,places.t+index.a)

function addlibtypeseq(l:linklists2,s:seq.libtype) ipair(linklists2)
let x =@(addele,identity,trackele(l,empty:seq.int),s)
    let t = linklists2(a.l.x + C64.0 + C64.length.s, wordthread.l.x, offsetthread.l.x, wordseqthread.l.x)
    ipair(place.l.x,@(addoffset,identity,t,places.x) )

function addmytypeseq(l:linklists2,s:seq.mytype) ipair(linklists2)
let x =@(addele,identity,trackele(l,empty:seq.int),s)
    let t = linklists2(a.l.x + C64.0 + C64.length.s, wordthread.l.x, offsetthread.l.x, wordseqthread.l.x)
    ipair(place.l.x,@(addoffset,identity,t,places.x) )

function addlibmodseq(l:linklists2,s:seq.libmod) ipair(linklists2)
let x =@(addele,identity,trackele(l,empty:seq.int),s)
    let t = linklists2(a.l.x + C64.0 + C64.length.s, wordthread.l.x, offsetthread.l.x, wordseqthread.l.x)
    ipair(place.l.x,@(addoffset,identity,t,places.x) )

function addlibsymseq(l:linklists2,s:seq.libsym) ipair(linklists2)
let x =@(addele,identity,trackele(l,empty:seq.int),s)
    let t = linklists2(a.l.x + C64.0 + C64.length.s, wordthread.l.x, offsetthread.l.x, wordseqthread.l.x)
    ipair(place.l.x,@(addoffset,identity,t,places.x) )

function addoffset(l:linklists2,index:int) linklists2
linklists2(a.l+C64.packit(offsetthread.l, index),wordthread.l,place.l,wordseqthread.l)
  
function addlibsym(l1:linklists2,sym:libsym) ipair(linklists2)
    let a = addwordseq(l1,returntype.sym)
   let b =addwordseq(value.a,instruction.sym)
   let l=value.b
   let l2=linklists2(a.l+C64.packit(wordthread.l,word33.fsig.sym),place.l,offsetthread.l,wordseqthread.l)
   let l3=linklists2(a.l2+C64.packit(offsetthread.l2, index.a),wordthread.l2,place.l2,wordseqthread.l2)
   let l4=linklists2(a.l3+C64.packit(offsetthread.l3, index.b),wordthread.l3,place.l3,wordseqthread.l3)
   ipair(place.l,l4)
   
Function addliblib(lin:linklists2,t:liblib) ipair(linklists2)
   let a = addwordseq(lin,libname.t)
   let b =addlibtypeseq(value.a,types.t)
      let c =addlibmodseq(value.b,mods.t)
   let l=value.c
     let l5=l+a+b+c+timestamp.t+toint.readonly.t 
   ipair(place.l,l5)

function addlibtype(lin:linklists2,t:libtype) ipair(linklists2)
   let a = addmytypeseq(lin,subtypes.t)
   let b =addwordseq(value.a,fldnames.t)
   let l=value.b
     let l5=l+name.t+toint.abstract.t+kind.t+a+TSIZE.size.t+LIT.size.t+b  
   ipair(place.l,l5)
   
function addlibmod(lin:linklists2,mod:libmod) ipair(linklists2)
   let a = addlibsymseq(lin,defines.mod)
   let b =addlibsymseq(value.a,exports.mod)
   let l=value.b
     let l5=l+toint.parameterized.mod+modname.mod+a+b+library.mod   
   ipair(place.l,l5)

function +(l:linklists2,i:int) linklists2 
   linklists2(a.l+C64.i,wordthread.l,offsetthread.l,wordseqthread.l)   

function +(l:linklists2,w:word) linklists2 
   linklists2(a.l+C64.packit(wordthread.l,word33.w),place.l,offsetthread.l,wordseqthread.l)   

function +(l:linklists2,b:ipair.linklists2) linklists2 
  linklists2(a.l+C64.packit(offsetthread.l, index.b),wordthread.l,place.l,wordseqthread.l)
 
Function addwordseq(t:linklists2, a:seq.word) ipair(linklists2)
ipair(place.t, linklists2(a.t + @(+, C64word33, [ C64.wordseqthread.t, C64.length.a], a), wordthread.t, offsetthread.t, place.t))

function C64word33(a:word)int C64.word33.a

function cast2int(s:seq.int)int builtin.NOOP
______________________________

Three Functions to pack two ints into 64 bits

function halfsize int // 2^31 // 2147483648

Function getlink(a:int)int toint(bits.a >> 31) - halfsize

Function packit(link:int, b:int)int toint(bits(halfsize + link)<< 31 ∨ bits.b)

Function getb(a:int)int toint(bits.a ∧ bits(halfsize - 1))

Function IDXUC(int, int)int builtin.IDXUC

Function cast2wordseq(int)seq.word builtin.NOOP

