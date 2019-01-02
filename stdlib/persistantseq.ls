Module persistantseq.T

use fileio

use internalbc

use ipair.linklists2

use libscope

use llvm

use persistant

use process.seq.T

use process.seq.word

use reconstruct

use seq.T

use stdlib

use textio

function addele(t:trackele, s:T)trackele 
 let a = addrecord(l.t, s)
  trackele(value.a, places.t + index.a)

function addrecord(linklists2, s:T)ipair.linklists2 unbound

Function addseq(l:linklists2, s:seq.T)ipair.linklists2 
 let x = @(addele, identity, trackele(l, empty:seq.int), s)
  let t = linklists2(a.l.x + C64.0 + C64.length.s, wordthread.l.x, offsetthread.l.x, wordseqthread.l.x)
  ipair(place.l.x, @(addoffset, identity, t, places.x))

function identityf(s:seq.T)seq.T s

Function flush(s:erecord.T)seq.word 
 if ispersistant.s 
  then let p = process.createlib2.s 
   result.p 
  else"Encoding is not persistant."

Function createlib2(s:erecord.T)seq.word 
 let thedata = result.process.identityf.mapping.s 
  let libname = merge("Q"+ name.s)
  let symtab ="libname initlib5 words wordlist list init22"
  // let z1 = createfile("stat.txt", ["in createlib2.1"])// 
  let discard = @(+, C, 0, symtab)
  let data1 = addseq(createlinkedlists, thedata)
  let liblib = addliblib(value.data1, emptyliblib.libname)
  // let z2 = createfile("stat.txt", ["in createlib2.2"])// 
  let data = value.liblib 
  let words = worddata 
  let worddatatype = array(length.words + 2, i64)
  let wordstype = array(2 + wordcount, i64)
  // let z3 = createfile("stat.txt", ["in createlib2.3"])// 
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
  // let z4 = createfile("stat.txt", ["in createlib2.4"])// 
  let b = createlib(llvm(deflist, bodytxts, typerecords), libname,"")
  {"OK"}

