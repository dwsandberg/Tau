Module llvmcode

use UTF8

use otherseq.addrsym

use bits

use seq.byte

use process.seq.byte

use seq.seq.byte

use bitcast.dummyrec2

use file

use seq.file

use format

use process.int

use seq.int

use bitcast.seq.int

use seq.mytype

use standard

use symbol2

use tausupport

Export type:callconfig

type callconfig is a:int

Function callfunc:callconfig(ctsym:symbol, typedict:typedict, stk:seq.int) seq.int
callfunc(ctsym, typedict, stk)

Function addbcwords(fn:seq.byte) int
let chars = decodeUTF8.UTF8(getfile.fn << 16),
for acc = empty:seq.char, c ∈ chars do
 if c = bcwordsep then
  let discard0 = encodeword.acc,
  empty:seq.char
 else
  acc + c
/do 0

Function getbcwords(fn:filename) seq.char getbcwords3.fn

function >1(a:addrsym, b:addrsym) ordering addr.a >1 addr.b

builtin addresssymbols seq.seq.addrsym

function addrsymX seq.addrsym
for acc = empty:seq.addrsym, e ∈ addresssymbols do acc + e /do acc

Function bcwordsep char char.255

builtin callstack(n:int) seq.int

Function getbcwords3(fn:filename) seq.char decodeUTF8.UTF8(getfile.tocstr.fullname.fn << 16)

function lookup(s1:symbol, s2:symbol, s3:symbol) seq.int
for a1 = 0, a2 = 0, a3 = 0, a ∈ addrsymX do
 next(if sym.a = s1 then addr.a else a1
  , if sym.a = s2 then addr.a else a2
  , if sym.a = s3 then addr.a else a3)
/do [a1, a2, a3]

Function stackTraceImp seq.word
let t = sort.addrsymX,
for txt = "/p", r ∈ callstack.30 << 2 do
 let i = binarysearch(t, addrsym(r, Lit.1)),
 txt + %.r + if between(-i - 1, 1, length.t) then %.sym.t_(-i - 1) else "" /if
 + "/br"
/do txt

________________

Function tocstr(w:word) seq.byte
{returns 16 bytes of header followed by UTF8 bytes endding with 0 byte. }
packed(toseqbyte(emptyUTF8 + decodeword.w) + tobyte.0)

builtin getbytefile2(seq.byte) process.seq.byte {OPTION STATE}

Function getfiles(args:seq.word) seq.file
for acc = empty:seq.file, fn ∈ getfilenames(args << 1) do
 let a = getbytefile2.tocstr.fullname.fn
 assert not.aborted.a report "Error openning file:" + fullname.fn,
 acc + file(fn, result.a + body2.a)
/do acc

builtin createfile3(data:seq.seq.byte, filename:seq.byte) int

function getfile(fn:seq.byte) seq.byte
let a = getbytefile2.fn
assert not.aborted.a report "Error openning file:",
result.a + body2.a

___________

function prepare(s:seq.seq.byte) seq.seq.byte
for acc = empty:seq.seq.byte, e ∈ s do
 if getseqtype.e = 1 then acc + e else acc + toseqseqbyte.e
/do packed.acc

Function finishentry(result:seq.file) UTF8
for acc = "files created:", f ∈ result do
 let discard2 = createfile3(prepare.rawdata.f, tocstr.fullname.fn.f),
 acc + fullname.fn.f
/do HTMLformat.acc

_______________

Function callfunc(ctsym:symbol, typedict:typedict, stk:seq.int) seq.int
let v = lookup(deepcopySym.resulttype.ctsym, deepcopySym.seqof.typeword, ctsym)
let funcaddress = v_3,
if funcaddress = 0 then
 empty:seq.int
else
 let p = createthread(c.bitcast:dummyrec2(toptr.packed(v + stk)), buildargcode(ctsym, typedict))
 assert not.aborted.p report message.p,
 [result.p]

Function buildargcode(sym:symbol, typedict:typedict) int
{needed because the call interface implementation for reals is different than other types is some implementations
 }
for acc = 1, typ ∈ paratypes.sym + resulttype.sym do
 acc * 2 + if basetype(typ, typedict) = typereal then 1 else 0
/do acc

type dummyparameterrecord is a:int, b:int

type dummyrec2 is a:int, b:int, c:dummyparameterrecord

builtin createthread(dummyparameterrecord, int) process.int 