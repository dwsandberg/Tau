Module inputoutput

use UTF8

use bits

use bitstream

use debuginfo

use file

use format

use standard

use symbol2

use tausupport

use typedict

use words

use otherseq.addrsym

use seq.addrsym

use seq.bit

use seq.bits

use seq.byte

use otherseq.char

use bitcast.dummyrec2

use seq.file

use process.int

use seq.int

use seq.mytype

use encoding.symaddresses

use seq.symaddresses

use otherseq.symbol

use seq.symbol

use seq.symdef

use set.symdef

use process.seq.bit

use seq.seq.bit

use bitcast.seq.bits

use bitcast.seq.byte

use process.seq.byte

use seq.seq.byte

use encoding.seq.char

use seq.seq.char

use bitcast.seq.int

use process.seq.int

Export type:cstr

Function tocstr(s:seq.word)cstr
let t = for acc = emptyUTF8, w ∈ s do acc + decodeword.w /for(toseqbyte.acc)
cstr.packed.bits.for acc = empty:bitstream, @e ∈ t + tobyte.0 do add(acc, bits.toint.@e, 8)/for(acc)

type cstr is dummy:seq.bits

Builtin getfile2(cstr)process.seq.int{OPTION STATE}

Builtin getbytefile2(cstr)process.seq.byte{OPTION STATE}

Builtin getbitfile2(cstr)process.seq.bit{OPTION STATE}

Function getfile:byte(name:seq.word)seq.byte
let a = getbytefile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.byte)

Function getfile:bit(name:seq.word)seq.bit
let a = getbitfile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.bit)

Builtin createfile3(a:seq.seq.byte, name:cstr)int

Function createfile(name:seq.word, a:seq.byte)int
createfile3(packed.toseqseqbyte.for acc = empty:bitstream, @e ∈ a do add(acc, bits.toint.@e, 8)/for(acc)
, tocstr.name
)

Function createfile(name:seq.word, a:seq.bits)int createfile3(packed.toseqseqbyte.tobitstream.a, tocstr.name)

type addrsym is addr:int, sym:symbol

function ?(a:addrsym, b:addrsym)ordering addr.a ? addr.b

Function stacktraceimp seq.word
let decode = symbolrefdecodeX
let t = 
 for t = empty:seq.addrsym, idx = 1, i ∈ symboladdress do next(t + addrsym(i, decode_idx), idx + 1)/for(sort.t)
for txt = " /p", r ∈ callstack.30 << 2 do
 let i = binarysearch(t, addrsym(r, Lit.1))
 txt + %.r
 + if between(-i - 1, 1, length.t)then print.sym.t_(-i - 1)else""/if
 + " /br"
/for(txt)

builtin callstack(n:int)seq.int

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

Function addlibwords(l:debuginfo)int
let discard = addencodings.words.l
1

___________

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

Function finishentry(result:seq.file)UTF8
for acc = "files created:", f ∈ result do
 let check = 
  for check = getseqtype.xdata.f = 0, p ∈ xdata.f while check do getseqtype.p = 1 /for(check)
 let discard2 = 
  if check then createfile3(packed.xdata.f, tocstr.[fullname.fn.f])
  else createfile([fullname.fn.f], data.f)
 acc + fullname.fn.f
/for(HTMLformat.acc)

Function getfiles(args:seq.word)seq.file
for acc = empty:seq.file, fn ∈ getfilenames(".", args << 1)do
 acc
 + if ext.fn ∈ "bc"then file(fn, empty:seq.seq.byte, [getfile:bit([fullname.fn])])
 else file(fn, [getfile:byte([fullname.fn])], empty:seq.seq.bit)
/for(acc)

function getfile(fn:filename)file file(fn, [getfile:byte([fullname.fn])], empty:seq.seq.bit) 