Module impDependent

use UTF8

use otherseq.addrsym

use bits

use seq.byte

use process.seq.byte

use seq.seq.byte

use encoding.seq.char

use seq.seq.char

use bitcast.dummyrec2

use file

use seq.file

use format

use process.int

use seq.int

use bitcast.seq.int

use seq.mytype

use standard

use encoding.symaddresses

use seq.symaddresses

use symbol

use seq.symbol

use symbol2

use set.symdef

use tausupport

Export type:debuginfo

type debuginfo is libname:seq.word
, words:seq.seq.char
, entrypointaddress:int
, symboladdress:seq.int
, profiledata:seq.parc
, symbolrefdecodeX:seq.symbol


type parc is caller:int, callee:int, counts:int, clocks:int, space:int, unused:int

Function =(a:parc, b:parc)boolean callee.a = callee.b ∧ caller.a = caller.b

Export type:parc

Export caller(parc)int

Export callee(parc)int

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

Builtin loadedLibs seq.debuginfo

Function symboladdress seq.int for acc = empty:seq.int, ll ∈ loadedLibs do acc + symboladdress.ll /for(acc)

Export symbolrefdecodeX(debuginfo)seq.symbol

Export words(debuginfo)seq.seq.char

Export profiledata(debuginfo)seq.parc

Function symbolrefdecodeX seq.symbol
for acc = empty:seq.symbol, ll ∈ loadedLibs do acc + symbolrefdecodeX.ll /for(acc)

Function dependentwords(dependentlibs:seq.word)seq.seq.char
for acc = empty:seq.seq.char, ll ∈ loadedLibs do
 if first.libname.ll ∈ dependentlibs then acc + words.ll else acc
/for(acc)

Function bcwordsep char char.255

Builtin getbcwords seq.byte

function addbcwords int
let b = getbcwords
for acc = empty:seq.char, c ∈ decodeUTF8.UTF8.b do
 if c = bcwordsep then
  let discard0 = encodeword.acc
  empty:seq.char
 else acc + c
/for(0)

Function addlibwords(l:debuginfo)int
if isempty.libname.l then addbcwords
else
 let discard = addencodings.words.l
 1

_______________

Function callfunc(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int
let t = funcaddress.ctsym
if t = 0 then empty:seq.int
else
 let adcret = funcaddress.deepcopySym.resulttype.ctsym
 let adc = funcaddress.deepcopySym.seqof.typeword
 let p = 
  createthread(adcret
  , adc
  , {funcaddress}t
  , c.bitcast:dummyrec2(toptr.packed.stk)
  , buildargcode(ctsym, typedict)
  )
 assert not.aborted.p report message.p
 [result.p]

function buildargcode(sym:symbol, typedict:typedict)int
{needed because the call interface implementation for reals is different than other types is some implementations}
for acc = 1, typ ∈ paratypes.sym + resulttype.sym do acc * 2 + if basetype(typ, typedict) = typereal then 1 else 0 /for(acc)

type dummyparameterrecord is a:int, b:int

type dummyrec2 is a:int, b:int, c:dummyparameterrecord

builtin createthread(int, int, int, dummyparameterrecord, int)process.int

function funcaddress(sym:symbol)int
let b = encodingdata:symaddresses
let symdefs = 
 tosymdefs.if length.b = 0 then
  let decode = symbolrefdecodeX
  for acc = empty:set.symdef, idx = 1, a ∈ symboladdress do next(acc + symdef(decode_idx, empty:seq.symbol, a), idx + 1)/for(decode.encode.symaddresses.acc)
 else b_1
let c = getSymdef(symdefs, sym)
if isempty.c then 0 else paragraphno.c_1

type symaddresses is tosymdefs:set.symdef

function =(symaddresses, symaddresses)boolean true

function hash(symaddresses)int 1

type addrsym is addr:int, sym:symbol

function ?(a:addrsym, b:addrsym)ordering addr.a ? addr.b

builtin callstack(n:int)seq.int

Function stackTraceImp seq.word
let decode = symbolrefdecodeX
let t = 
 for t = empty:seq.addrsym, idx = 1, i ∈ symboladdress do next(t + addrsym(i, decode_idx), idx + 1)/for(sort.t)
for txt = " /p", r ∈ callstack.30 << 2 do
 let i = binarysearch(t, addrsym(r, Lit.1))
 txt + %.r
 + if between(-i - 1, 1, length.t)then %.sym.t_(-i - 1)else""/if
 + " /br"
/for(txt)

________________

function tocstr(w:word)seq.byte
{returns 16 bytes of header followed by UTF8 bytes endding with 0 byte. }
packed(toseqbyte(emptyUTF8 + decodeword.w) + tobyte.0)

builtin getbytefile2(seq.byte)process.seq.byte{OPTION STATE}

Function getfiles(args:seq.word)seq.file
for acc = empty:seq.file, fn ∈ getfilenames(args << 1)do
 let a = getbytefile2.tocstr.fullname.fn
 assert not.aborted.a report"Error openning file:" + fullname.fn
 acc + file(fn, result.merge(a, result.a + body2.a, empty:seq.byte))
/for(acc)

builtin createfile3(data:seq.seq.byte, filename:seq.byte)int

___________

Function prepare(s:seq.seq.byte)seq.seq.byte
for acc = empty:seq.seq.byte, e ∈ s do
 if getseqtype.e = 1 then acc + e else acc + toseqseqbyte.e
/for(packed.acc)

Function finishentry(result:seq.file)UTF8
for acc = "files created:", f ∈ result do
 let discard2 = createfile3(prepare.rawdata.f, tocstr.fullname.fn.f)
 acc + fullname.fn.f
/for(HTMLformat.acc) 