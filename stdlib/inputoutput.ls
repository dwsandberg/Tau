Module inputoutput

use UTF8

use bits

use bitstream

use libraryModule

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

use process.int

use seq.int

use seq.liblib

use seq.mytype

use encoding.symaddresses

use seq.symaddresses

use otherseq.symbol

use seq.symbol

use seq.symdef

use set.symdef

use process.seq.bit

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
let t = 
 for acc = empty:seq.addrsym, ll ∈ loadedLibs do
  for t = acc, idx = 1, i ∈ symboladdress.ll do next(t + addrsym(i, decode(symbolref.idx, ll)), idx + 1)/for(t)
 /for(sort.acc)
for txt = " /p", r ∈ callstack.30 << 2 do
 let i = binarysearch(t, addrsym(r, Lit.1))
 txt + %.r
 + if between(-i - 1, 1, length.t)then print.sym.t_(-i - 1)else""/if
 + " /br"
/for(txt)

builtin callstack(n:int)seq.int

Builtin loadedLibs seq.liblib

function funcaddress(sym:symbol)int
let b = encodingdata:symaddresses
let symdefs = 
 tosymdefs.if length.b = 0 then
  for acc = empty:set.symdef, ll ∈ loadedLibs do
   for acc1 = acc, idx = 1, a ∈ symboladdress.ll do next(acc1 + symdef(decode(symbolref.idx, ll), empty:seq.symbol, a), idx + 1)/for(acc1)
  /for(decode.encode.symaddresses.acc)
 else b_1
let c = getSymdef(symdefs, sym)
if isempty.c then 0 else paragraphno.c_1

type symaddresses is tosymdefs:set.symdef

function =(symaddresses, symaddresses)boolean true

function hash(symaddresses)int 1

Function dependentwords(dependentlibs:seq.word)seq.seq.char
for acc0 = empty:seq.seq.char, ll ∈ loadedLibs do
 if first.libname.ll ∈ dependentlibs then
  for acc = acc0, p ∈ words.ll do acc + data.p /for(acc)
 else acc0
/for(acc0)

Function dependentinfo(dependentlibs:seq.word)midpoint
for org = empty:midpoint, ll ∈ loadedLibs do
 let libname = (libname.ll)_1
 if libname ∈ dependentlibs then tomidpoint(org, ll, libname)else org
/for(org)

Function addlibwords(l:liblib)int
let discard = addencodingpairs.words.l
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

Function checkload seq.word
for yy = "", ll ∈ loadedLibs do
 for acc = yy, p ∈ words.ll do
  if code.p = asencoding.encodeword.data.p then acc else acc + encodeword.data.p
 /for(acc)
/for(yy) 