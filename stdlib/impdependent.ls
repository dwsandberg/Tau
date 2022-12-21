Module impDependent

use UTF8

use otherseq.addrsym

use bits

use seq.byte

use process.seq.byte

use seq.seq.byte

use seq.seq.char

use seq.debuginfo

use bitcast.dummyrec2

use file

use seq.file

use format

use process.int

use seq.int

use bitcast.seq.int

use otherseq.mytype

use seq.mytype

use otherseq.seq.mytype

use standard

use seq.symbol

use symbol2

use set.symdef

use tausupport

Export type:debuginfo

Export words(debuginfo) seq.seq.char

type debuginfo is libname:seq.word
 , words:seq.seq.char
 , entrypointaddress:int
 , addressSymbol:seq.addrsym
 , bytes:seq.byte

builtin loadedLibs seq.debuginfo

Function dependentwords(dependentlibs:seq.word) seq.seq.char
for acc = empty:seq.seq.char, ll ∈ loadedLibs do
 if first.libname.ll ∈ dependentlibs then acc + words.ll else acc
/for (acc)

Function bcwordsep char char.255

Builtin getbcwords seq.byte

function addbcwords int
let b = getbcwords
for acc = empty:seq.char, c ∈ decodeUTF8.UTF8.b do
 if c = bcwordsep then
  let discard0 = encodeword.acc
  empty:seq.char
 else
  acc + c
/for (0)

Function addlibwords(l:debuginfo) int
if isempty.libname.l then
 addbcwords
else
 let discard = addencodings.words.l
 1

_______________

Function callfunc(ctsym:symbol, typedict:typedict, stk:seq.int) seq.int
let v = lookup(ctsym, deepcopySym.resulttype.ctsym, deepcopySym.seqof.typeword)
let funcaddress = v_1
if funcaddress = 0 then
 empty:seq.int
else
 let p = 
  createthread({address of deepcopy for resulttype of function} v_2
   , {address of deepcopy for seq.word} v_3
   , funcaddress
   , c.bitcast:dummyrec2(toptr.packed.stk)
   , buildargcode(ctsym, typedict))
 assert not.aborted.p report message.p
 [result.p]

function buildargcode(sym:symbol, typedict:typedict) int
{needed because the call interface implementation for reals is different than other types is some implementations
 }
for acc = 1, typ ∈ paratypes.sym + resulttype.sym do
 acc * 2 + if basetype(typ, typedict) = typereal then 1 else 0
/for (acc)

type dummyparameterrecord is a:int, b:int

type dummyrec2 is a:int, b:int, c:dummyparameterrecord

builtin createthread(int, int, int, dummyparameterrecord, int) process.int

type addrsym is addr:int, sym:symbol

function >1(a:addrsym, b:addrsym) ordering addr.a >1 addr.b

builtin callstack(n:int) seq.int

function addrsym seq.addrsym
for acc = empty:seq.addrsym, ll ∈ loadedLibs do acc + addressSymbol.ll /for (acc)

function %(a:addrsym) seq.word "$(addr.a) $(sym.a)"

Function checkIT(input:seq.file, o:seq.word) seq.file
{should not need this function}
[file(o, "Hi")]

function lookup(s1:symbol, s2:symbol, s3:symbol) seq.int
for a1 = 0, a2 = 0, a3 = 0, a ∈ addrsym do
 next(if sym.a = s1 then addr.a else a1
  , if sym.a = s2 then addr.a else a2
  , if sym.a = s3 then addr.a else a3)
/for ([a1, a2, a3])

Function stackTraceImp seq.word
let t = sort.addrsym
for txt = "/p", r ∈ callstack.30 << 2 do
 let i = binarysearch(t, addrsym(r, Lit.1))
 txt + %.r + if between(-i - 1, 1, length.t) then %.sym.t_(-i - 1) else "" /if
 + "/br"
/for (txt)

________________

function tocstr(w:word) seq.byte
{returns 16 bytes of header followed by UTF8 bytes endding with 0 byte. }
packed(toseqbyte(emptyUTF8 + decodeword.w) + tobyte.0)

builtin getbytefile2(seq.byte) process.seq.byte {OPTION STATE}

Function getfiles(args:seq.word) seq.file
for acc = empty:seq.file, fn ∈ getfilenames(args << 1) do
 let a = getbytefile2.tocstr.fullname.fn
 assert not.aborted.a report "Error openning file:" + fullname.fn
 acc + file(fn, result.a + body2.a)
/for (acc)

builtin createfile3(data:seq.seq.byte, filename:seq.byte) int

___________

Function prepare(s:seq.seq.byte) seq.seq.byte
for acc = empty:seq.seq.byte, e ∈ s do
 if getseqtype.e = 1 then acc + e else acc + toseqseqbyte.e
/for (packed.acc)

Function finishentry(result:seq.file) UTF8
for acc = "files created:", f ∈ result do
 let discard2 = createfile3(prepare.rawdata.f, tocstr.fullname.fn.f)
 acc + fullname.fn.f
/for (HTMLformat.acc) 