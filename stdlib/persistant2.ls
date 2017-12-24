module persistant2

use ipair.linklists2

use libscope

use llvm

use oseq.word

use prims

use process.int

use process.liblib

use processtypes

use reconstruct

use seq.constmap

use seq.encoding.llvmtype

use seq.int

use seq.liblib

use seq.libmod

use seq.libsym

use seq.libtype

use seq.linklists2

use seq.mytype

use seq.word3

use set.libtype

use set.word

use stacktrace

use stdlib

use internalbc

type word3encoding is encoding word3

Function wordcount int length.mapping.word3encoding

Function worddata seq.int 
 let ws = mapping.word3encoding 
  @(+, eword, [ C64.0, C64.length.ws], ws)

_________________

encode Functions

The linklists2 type contains a seq of integers that represents the memory. Any memory locations that store the type word are linked into a linked list begining with wordthread. Two values are packed into the integer is store in the seq.One is the word3 encoding and the other the next value in the linked list. Any memory locations that store an address of another memory are linked into a linked list beginning with offsetthread. In this case the element in the seq is represents two interger values. One is the next value in the linked list and the other is the index of the refrenced memory location.

type linklists2 is record a:seq.int, wordthread:int, offsetthread:int, start:int

Function a(linklists2)seq.int export

Function initializer(conststype:encoding.llvmtype, data:linklists2)int 
 C(conststype, [ AGGREGATE, C64.0, C64(length.a.data + 3), C64.wordthread.data, C64.offsetthread.data, C64.0]+ a.data)+ 1

Function linklists2(a:seq.int, wordthread:int, offsetthread:int, start:int)linklists2 export

type word3 is record toword:word

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

Function place(a:linklists2)int start.a + length.a.a + 1

Function word33(a:word)int encoding.encode(word3.a, word3encoding)

function addword(p:partobject2, w:word)partobject2 
 let e3 = linklists2(a.subobjects.p, mainplace.p, offsetthread.subobjects.p, start.subobjects.p)
  partobject2(mainobj.p + C64.packit(wordthread.subobjects.p, encoding.encode(word3.w, word3encoding)), mainstart.p, e3)

function addref(p:partobject2, e3:linklists2, location:int)partobject2 
 let e4 = linklists2(a.e3, wordthread.e3, mainplace.p, start.e3)
  partobject2(mainobj.p + [ C64.packit(offsetthread.e3, location)], mainstart.p, e4)

Type build object is used to construct object. First the space is allocated for it.Then for each field if the next field of object is pointer then the subobject is created.A value for the field or relocation information is place in the field before going on to the next fld.

type partobject2 is record mainobj:seq.int, mainstart:int, subobjects:linklists2

function mainplace(t:partobject2)int length.mainobj.t + 1 + mainstart.t

function +(a:partobject2, x:int)partobject2 partobject2(mainobj.a + [ x], mainstart.a, subobjects.a)

function allocate(t:linklists2, size:int)partobject2 
 partobject2(a.t, start.t, linklists2(empty:seq.int, wordthread.t, offsetthread.t, size + start.t + length.a.t))

function eword(w:word3)seq.int 
 let a = decode.toword.w 
  @(+, C64, [ C64.0, C64.length.a], a)

Function addconst(constants:seq.seq.word, t:linklists2, constnumber:int)ipair.linklists2 
 let d = constants_constnumber 
  let loc = place.t 
  let a = decode(encode(constmap(constnumber, loc), cmap), cmap)
  if offset.a < loc 
  then ipair(offset.a, t)
  else let len = toint(d_2)
  // assert len = toint.d_6 + 2 report"CONST FORMAT?"+ d // 
  ipair(loc, subfields(constants, allocate(t, len), d, 3))

function subfields(constants:seq.seq.word, p:partobject2, d:seq.word, i:int)linklists2 
 if i > length.d 
  then // finish the object by combining mainobj with subobjects // 
   linklists2(mainobj.p + a.subobjects.p, wordthread.subobjects.p, offsetthread.subobjects.p, mainstart.p)
  else if d_i ="LIT"_1 
  then subfields(constants, p + C64.toint(d_(i + 1)), d, i + 2)
  else if d_i ="FREF"_1 
  then let arg = d_(i + 1)
   // assert false report [ arg]// 
   subfields(constants, p + C(i64, [ CONSTCECAST, 9, typ.ptr.getftype.arg, C.[ arg]]), d, i + 2)
  else let newp = if d_i ="WORD"_1 
   then // add a word. This requires adding information for re-encoding word. // addword(p, d_(i + 1))
   else assert d_i ="CONST"_1 report [ d_i]
   // add object of type b_i. This requires adding information for relocation.// 
   let cst = addconst(constants, subobjects.p, toint(d_(i + 1)))
   addref(p, value.cst, index.cst)
  // now process remaining fields // subfields(constants, newp, d, i + 2)

type constmap is record constnumber:int, offset:int

type cmap is encoding constmap

function =(a:constmap, b:constmap)boolean constnumber.a = constnumber.b

function hash(a:constmap)int hash.constnumber.a

function print(a:constmap)seq.word [ toword.constnumber.a, toword.offset.a]+"&br"

Function getftype(w:word)encoding.llvmtype 
 let a = @(+, count.90, 1, decode.w)
  function.constantseq(a, i64)

function count(val:int, i:int)int if val = i then 1 else 0

function cast2int(liblib)int builtin

function cast2intseq(int)seq.int builtin

function cast2word(int)word builtin

Function prepareliblib(mylib:liblib)linklists2 
 let alltypes = asset.@(+, types, empty:seq.libtype, libs)
  addobject(alltypes, mytype."liblib", linklists2(empty:seq.int, 0, 0, 3), cast2int.result.process.identity.mylib)

function addobject(alltypes:set.libtype, a:mytype, t:linklists2, d:int)linklists2 
 // assert a in [ mytype."int", mytype."word", mytype."word seq", mytype."int seq seq", mytype."liblib", mytype."libtype seq", mytype."libtype", mytype."mytype seq", mytype."mytype"]report"??"+ towords.a // 
  if a in [ mytype."word seq", mytype."mytype"]
  then t + cast2wordseq.d 
  else if abstracttype.a ="seq"_1 
  then let s = cast2intseq.d 
   subseq(alltypes, allocate(t, length.s + 2)+ C64.0 + C64.length.s, s, parameter.a, 1)
  else let b = deepcopytypes2(alltypes, a)
  subfields(alltypes, allocate(t, length.b), d, b, 1)

function subfields(alltypes:set.libtype, p:partobject2, data:int, b:seq.mytype, i:int)linklists2 
 if i > length.b 
  then // finish the object by combining mainobj with subobjects // 
   linklists2(mainobj.p + a.subobjects.p, wordthread.subobjects.p, offsetthread.subobjects.p, mainstart.p)
  else if b_i in [ mytype."int", mytype."real"]
  then subfields(alltypes, p + C64.IDXUC(data, i - 1), data, b, i + 1)
  else let newp = if b_i = mytype."int seq encoding"
   then // add a word. This requires adding information for re-encoding word. // 
    let w = cast2word.IDXUC(data, i - 1)
    let e3 = linklists2(a.subobjects.p, mainplace.p, offsetthread.subobjects.p, start.subobjects.p)
    partobject2(mainobj.p + C64.packit(wordthread.subobjects.p, word33.w), mainstart.p, e3)
   else // add object of type b_i. This requires adding information for relocation.// 
   let e3 = addobject(alltypes, b_i, subobjects.p, IDXUC(data, i - 1))
   let e4 = linklists2(a.e3, wordthread.e3, mainplace.p, start.e3)
   partobject2(mainobj.p + [ C64.packit(offsetthread.e3, place.subobjects.p)], mainstart.p, e4)
  // now process remaining fields // subfields(alltypes, newp, data, b, i + 1)

function subseq(alltypes:set.libtype, p:partobject2, s:seq.int, elementtype:mytype, i:int)linklists2 
 if i > length.s 
  then // finish the object by combining mainobj with subobjects // 
   linklists2(mainobj.p + a.subobjects.p, wordthread.subobjects.p, offsetthread.subobjects.p, mainstart.p)
  else if elementtype in [ mytype."int", mytype."real"]
  then subseq(alltypes, p + C64(s_i), s, elementtype, i + 1)
  else let newp = if elementtype = mytype."int seq encoding"
   then // add a word. This requires adding information for re-encoding word. // 
    let w = cast2word(s_i)
    let e3 = linklists2(a.subobjects.p, mainplace.p, offsetthread.subobjects.p, start.subobjects.p)
    partobject2(mainobj.p + C64.packit(wordthread.subobjects.p, word33.w), mainstart.p, e3)
   else // add object of elementtype. This requires adding information for relocation.// 
   let e3 = addobject(alltypes, elementtype, subobjects.p, s_i)
   let e4 = linklists2(a.e3, wordthread.e3, mainplace.p, start.e3)
   partobject2(mainobj.p + [ C64.packit(offsetthread.e3, place.subobjects.p)], mainstart.p, e4)
  // now process remaining elements // subseq(alltypes, newp, s, elementtype, i + 1)

function +(t:linklists2, a:word)linklists2 
 linklists2(a.t + [ C64.packit(wordthread.t, word33.a)], place.t, offsetthread.t, start.t)

function +(t:linklists2, a:seq.word)linklists2 
 @(+, identity, linklists2(a.t + [ C64.0, C64.length.a], wordthread.t, offsetthread.t, start.t), a)

Function addseqword(t:linklists2, a:seq.word)ipair.linklists2 ipair(place.t, t + a)

function cast2int(s:seq.int)int builtin

function interface(l:liblib, dependlibs:seq.word)seq.word 
 let a = createlib(cast2int.empty:seq.int,"int seq", l, dependlibs)
  {"OK"}

Function interface(name:seq.word, modlist:seq.word, deplibs:seq.word)seq.word 
 let mods = @(+, findmods.modlist, empty:seq.libmod, libs)
  let alltypes = asset.@(+, types, empty:seq.libtype, libs)
  let llplus = @(∪, libtypes("cannot find type", alltypes), empty:set.libtype, [ mytype."liblib", 
  mytype."libtype", 
  mytype."libmod", 
  mytype."offset", 
  mytype."mytype", 
  mytype."libsym"])
  let types = @(∪, libtypes.alltypes, llplus, mods)
  interface(liblib(name, toseq.types, mods, true), deplibs)+ @(seperator."&br", print,"", toseq.types)

function findmods(keep:seq.word, l:liblib)seq.libmod @(+, findmod.keep, empty:seq.libmod, mods.l)

function findmod(keep:seq.word, m:libmod)seq.libmod 
 if modname.m in keep then [ m]else empty:seq.libmod

function libtypes(s:set.libtype, a:libmod)set.libtype 
 @(∪, libtypes.s, empty:set.libtype, exports.a + defines.a)

Function createlib2(thedata:int, typeindexfunction:int, libname:word, dependlibs:seq.word)int 
 let thetype = towords.parameter.modname.tosyminfo.addresstosymbol.typeindexfunction 
  let mymod = libmod(false, libname, empty:seq.libsym, empty:seq.libsym, libname)
  let mylib = liblib([ libname], empty:seq.libtype, [ mymod])
  createlib(thedata, thetype, mylib,"")

function createlib(thedata:int, thetype:seq.word, mylib:liblib, dependlibs:seq.word)int 
 // must call as process so that the encodings start out empty // 
  result.process.createlibp(thedata, thetype, mylib, dependlibs)

function createlibp(thedata:int, thetype:seq.word, mylib:liblib, dependlibs:seq.word)int 
 let libname = libname(mylib)_1 
  let symtab ="libname initlib4 words wordlist list liblib init22"
  let discard = @(+, C, 0, symtab)
  let alltypes = asset.@(+, types, empty:seq.libtype, libs)
  let data = addobject(alltypes, mytype(thetype +"seq"), linklists2(empty:seq.int, 0, 0, 3), thedata)
  let lib = addobject(alltypes, mytype."liblib", linklists2(empty:seq.int, 0, 0, 3), cast2int.result.process.identity.mylib)
  let words = worddata 
  let worddatatype = array(length.words + 2, i64)
  let libdesctype = array(length.a.lib + 5, i64)
  let wordstype = array(2 + wordcount, i64)
  let conststype = array(length.a.data + 5, i64)
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
  typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64, ptr.i64], 
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
  typ.conststype, 
  2, 
  C(conststype, [ AGGREGATE, C64.0, C64(length.a.data + 3), C64.wordthread.data, C64.offsetthread.data, C64.0]+ a.data)+ 1, 
  3, 
  align8 + 1, 
  0], 
  [ MODULECODEGLOBALVAR, 
  typ.libdesctype, 
  2, 
  C(libdesctype, [ AGGREGATE, C64.0, C64(length.a.lib + 3), C64.wordthread.lib, C64.offsetthread.lib, C64.0]+ a.lib)+ 1, 
  3, 
  align8 + 1, 
  0], 
  // init22 // [ MODULECODEFUNCTION, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
  let bodytxts = [BLOCKCOUNT(1, 1)+CALL(1, 
  0, 
  32768, 
  typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64, ptr.i64], 
  C."initlib4", 
  libnameptr, 
  getelementptr(wordstype,"words"), 
  getelementptr(worddatatype,"wordlist"), 
  getelementptr(conststype,"list"), 
  getelementptr(libdesctype,"liblib"))+RET(3)]
   createlib(llvm( deflist, bodytxts, typerecords), libname,"")

