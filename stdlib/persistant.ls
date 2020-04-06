Module persistant

use UTF8

use bits

use encoding.seq.char

use persistantseq.encodingrep.seq.char

use seq.encodingrep.seq.char

use set.encodingrep.seq.char

use encoding.const3

use seq.const3

use blockseq.flddesc

use blockseq.seq.flddesc

use seq.seq.flddesc

use seq.flddesc

use set.flddesc

use seq.liblib

use persistantseq.libmod

use seq.libmod

use libscope

use persistantseq.libsym

use seq.libsym

use deepcopy.linklists2

use ipair.linklists2

use seq.linklists2

use llvm

use persistantseq.mytype

use seq.mytype

use stdlib

use seq.tree.seq.word

use stack.tree.seq.word

use tree.seq.word

use encoding.word3

use seq.encodingrep.word3

use seq.word3

use words


Function type:linklists2 internaltype export

type linklists2 is record a:seq.int 


function linklists2(seq.int) linklists2 export 
 

Function createlinkedlists linklists2 linklists2(empty:seq.int)

type word3encoding is encoding word3

function assignencoding(l:int, a:word3) int assignrandom(l,a)


Function wordcount int length.orderadded.word3encoding

Function worddata seq.int
let ws = orderadded.word3encoding
 @(+, eword, [ C64.0, C64.length.ws], ws)

_________________

encode Functions


Function a(linklists2)seq.int export

Function length( data:linklists2) int length.a.data+ 5


Function initializer(conststypex:llvmtype, data:linklists2)int
 C(conststypex, [ AGGREGATE,  C64.0, C64(length.a.data + 3), C64.0, C64.0, C64.0]  +  a.data)
 + 1

type word3 is record toword:word

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

Function place(a:linklists2)int length.a.a + 4

Function registerword(a:word)int
 let d = encode(word3encoding, word3.a)
  0

function eword(w:word3)seq.int
 let a = tointseq.decodeword.toword.w
  @(+, C64, [ C64.0, C64.length.a], a)

function eword2(w:word3)encodingrep.seq.char
 let a = decodeword.toword.w
  encodingrep(asencoding.toword.w, a, hash.a)

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

function assignencoding(l:int, a:const3) int assignrandom(l,a)


Function addconst(l:linklists2, fullinst:seq.word)ipair.linklists2 addconst(l, buildconsttree(fullinst, 2, empty:stack.tree.seq.word))

function buildconsttree(s:seq.word, i:int, result:stack.tree.seq.word)tree.seq.word
 if i + 1 > length.s then top.result
 else
  let c = subseq(s, i, i + 1)
   if c_1 = "CRECORD"_1 then
   let nosons = toint.c_2
     buildconsttree(s, i + 2, push(pop(result, nosons), tree(c, top(result, nosons))))
   else if c_1 = "WORDS"_1 then
   let len = toint.c_2
     // assert false report subseq(s, i, len + 1)//
     buildconsttree(s, i + len + 2, push(result, tree.subseq(s, i, i + len + 1)))
   else buildconsttree(s, i + 2, push(result, tree.c))

function addconst(l:linklists2, t:tree.seq.word)ipair.linklists2
 // First build description of record. This may add other const records to l //
 let y = @(getindex, identity, trackflds(l, empty:seq.flddesc, 1), sons.t)
  // look up CRECORD to see if we have already used it. //
  let x = decode(const3e, encode(const3e, const3(place.l.y, flds.y)))
   if place.x ≠ place.l.y then ipair(place.x, l.y)
   else
    // have seen this CRECORD before so process it //
    let newlist = @(buildtheobject.place.l.y, identity, l.y, flds.x)
     ipair(place.l.y, newlist)

function getindex(f:trackflds, t:tree.seq.word)trackflds
 let typ =(label.t)_1
  if typ = "LIT"_1 then
  trackflds(l.f, flds.f + flddesc(C64.toint.(label.t)_2,"LIT"_1), if state.f = 1 ∧ label.t = "LIT 0"then 2
   else if state.f = 2 then 3 else 0)
  else if typ = "WORD"_1 then
  let discard = registerword.(label.t)_2
    trackflds(l.f, flds.f + flddesc(C64.hash.(label.t)_2,"LIT"_1), if state.f = 3 then 3 else 0)
  else if typ = "WORDS"_1 then
  // assert false report"in get index"+ subseq(label.t, 3, length.label.t)//
   let k = addwordseq(l.f, subseq(label.t, 3, length.label.t))
    trackflds(value.k, flds.f + flddesc(index.k,"CRECORD"_1), 0)
  else if typ = "FREF"_1 then
  trackflds(l.f
   , flds.f
   + flddesc(C(i64, [ CONSTCECAST, 9, typ.ptr.getftype.(label.t)_2, C.[(label.t)_2]]),"LIT"_1)
   , 0)
  else
   assert(label.t)_1 = "CRECORD"_1 report"PROBLEM"
   let k = addconst(l.f, t)
    trackflds(value.k, flds.f + flddesc(index.k,"CRECORD"_1), 0)

Function buildtheobject(objectstart:int, l:linklists2, d:flddesc)linklists2
 FORCEINLINE
 .if kind.d = "LIT"_1 then linklists2(a.l + index.d)
 else
    linklists2(a.l +  objectref( index.d ))

Function type:trackele internaltype export

type trackele is record l:linklists2, places:seq.int

function l(trackele)linklists2 export

function places(trackele)seq.int export

function trackele(l:linklists2, places:seq.int)trackele export

function addrecord(l:linklists2, s:mytype)ipair.linklists2 addwordseq(l, towords.s)

Function addoffset(l:linklists2, index:int)linklists2 linklists2(a.l + 
 objectref( index ))

function addrecord(l1:linklists2, sym:libsym)ipair.linklists2
 let a = addwordseq(l1, returntype.sym)
 let b = addwordseq(value.a, instruction.sym)
 let l = value.b
  ipair(place.l, l + fsig.sym + a + b)

function ?(a:encodingrep.seq.char, b:encodingrep.seq.char)ordering valueofencoding.code.a ? valueofencoding.code.b

Function addliblib(lin:linklists2, t:liblib)ipair.linklists2
 // assert libname.t ="stdlib"report libname.t //
 let a = addwordseq(lin, libname.t)
 let c = addseq(value.a, mods.t)
 let used = @(+, eword2, empty:seq.encodingrep.seq.char, orderadded.word3encoding)
 let have = if libname.t = "stdlib"then empty:seq.encodingrep.seq.char else words.loadedlibs_1
 let d = addseq(value.c, toseq(asset.used - asset.have))
 let l = value.d
 let l5 = l + a + d + c + timestamp.t + toint.readonly.t
  ipair(place.l, l5)

Function addrecord(lin:linklists2, e:encodingrep.seq.char)ipair.linklists2
 let k = addintseq(lin, tointseq.data.e)
 let l = value.k
  ipair(place.l, l + valueofencoding.code.e + k + hash.e)

function addrecord(lin:linklists2, modx:libmod)ipair.linklists2
 let a = addseq(lin, defines.modx)
 let b = addseq(value.a, exports.modx)
 let c = addseq(value.b, uses.modx)
 let l = value.c
 let l5 = l + toint.parameterized.modx + modname.modx + a + b + c
  ipair(place.l, l5)

Function +(l:linklists2, i:int)linklists2 linklists2(a.l + C64.i)

Function +(l:linklists2, w:word)linklists2
 let discard = registerword.w
  l + hash.w

Function +(l:linklists2, b:ipair.linklists2)linklists2
 linklists2(a.l +  objectref.index.b  )

Function addwordseq(t:linklists2, a:seq.word)ipair.linklists2
 let discard = @(+, registerword, 0, a)
  addintseq(t, @(+, hash, empty:seq.int, a))

Function addintseq(t:linklists2, s:seq.int)ipair.linklists2
 ipair(place.t, linklists2(a.t + @(+, C64, [ C64.0, C64.length.s], s)))

Function objectref(b:ipair.linklists2) int
let conststype = array(-2, i64)
    C(i64,[ CONSTCECAST, 9, typ.ptr.i64,getelementptr(conststype,"list", index.b+1)])   
    
Function objectref(idx:int) int
let conststype = array(-2, i64)
    C(i64,[ CONSTCECAST, 9, typ.ptr.i64,getelementptr(conststype,"list", idx+1)])   

    
 
     