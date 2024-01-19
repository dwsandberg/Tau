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

use seq.seq.file

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
let chars = decodeUTF8.UTF8(getfile.fn << 16)
for acc = empty:seq.char, c ∈ chars
do
 if c = bcwordsep then
  let discard0 = encodeword.acc,
  empty:seq.char
 else acc + c,
0

Function getbcwords(fn:filename) seq.char getbcwords3.fn

function >1(a:addrsym, b:addrsym) ordering addr.a >1 addr.b

builtin addresssymbols seq.seq.addrsym

use encoding.addrsym

function =(a:addrsym, b:addrsym) boolean sym.a = sym.b

function hash(a:addrsym) int hash.sym.a

use symbol

use seq.seq.addrsym

function lookup(sym:symbol) int
let data = encodingdata:addrsym
for acc = 0, e ∈ if n.data = 0 then addresssymbols else empty:seq.seq.addrsym
do
 for discard = acc, e2 ∈ e
 do
  let discard1 = encode.e2,
  discard,
 0
let t = findencode.addrsym(0, sym),
if isempty.t then 0 else addr.1#t

Function bcwordsep char char.255

builtin callstack(n:int) seq.int

Function getbcwords3(fn:filename) seq.char decodeUTF8.UTF8(getfile.tocstr.fullname.fn << 16)

Function stackTraceImp seq.word
for acc = empty:seq.addrsym, e ∈ addresssymbols
do acc + e
let t = sort.acc
for txt = "/p", r ∈ callstack.30 << 2
do
 let i = binarysearch(t, addrsym(r, Lit.1)),
 txt
  + %.r
  + (if between(-i - 1, 1, n.t) then %.sym.(-i - 1)#t else "")
  + "/br",
txt

-------------------------------

Function tocstr(w:word) seq.byte
{returns 16 bytes of header followed by UTF8 bytes ending with 0 byte.}
packed(toseqbyte(emptyUTF8 + decodeword.w) + tobyte.0)

builtin getbytefile2(seq.byte) process.seq.byte {OPTION STATE}

Function getfiles(b:seq.seq.filename) seq.seq.file
for acc = empty:seq.seq.file, fileNames ∈ b
do
 for acc1 = empty:seq.file, fn ∈ fileNames
 do
  let a = getbytefile2.tocstr.fullname.fn,
  acc1
   + if aborted.a then
   for UTF8msg = emptyUTF8, w ∈ "500 Error opening file"
   do UTF8msg + decodeword.w + char.32,
   file(fn, empty:seq.seq.byte, UTF8msg)
  else file(fn, [result.a + body2.a], emptyUTF8 + decodeword.1#"200"),
 acc + acc1
let err = errors.acc,
acc

builtin createfile3(data:seq.seq.byte, filename:seq.byte) int

function getfile(fn:seq.byte) seq.byte
let a = getbytefile2.fn
assert not.aborted.a report "Error openning file:",
result.a + body2.a

-------------------------------

function prepare(s:seq.seq.byte) seq.seq.byte
for acc = empty:seq.seq.byte, e ∈ s
do if getseqtype.e = 1 then acc + e else acc + toseqseqbyte.e,
packed.acc

Function finishentry(result:seq.file) UTF8
for acc = "files created:", f ∈ result
do
 let discard2 = createfile3(prepare.rawdata.f, tocstr.fullname.fn.f),
 acc + fullname.fn.f,
HTMLformat.acc

-------------------------------

Function callfunc(ctsym:symbol, typedict:typedict, stk:seq.int) seq.int
let v3 = lookup.ctsym,
if v3 = 0 then empty:seq.int
else
 let v1 = lookup.deepcopySym.resulttype.ctsym
 let v2 = lookup.deepcopySym.seqof.typeword
 let p = createthread(c.bitcast:dummyrec2(toptr.packed([v1, v2, v3] + stk)), buildargcode(ctsym, typedict)),
 assert not.aborted.p report message.p,
 [result.p]

function %(a:addrsym) seq.word %.sym.a + %.addr.a

Function buildargcode(sym:symbol, typedict:typedict) int
{needed because the call interface implementation for reals is different than other types is some implementations}
for acc = 1, typ ∈ paratypes.sym + resulttype.sym
do acc * 2 + if basetype(typ, typedict) = typereal then 1 else 0,
acc

type dummyparameterrecord is a:int, b:int

type dummyrec2 is a:int, b:int, c:dummyparameterrecord

builtin createthread(dummyparameterrecord, int) process.int 