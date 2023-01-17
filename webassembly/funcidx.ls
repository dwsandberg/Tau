Module funcidx

use bits

use seq.byte

use seq.seq.byte

use encoding.datax

use seq.datax

use encoding.efuncidx

use seq.efuncidx

use file

use encoding.frefindex

use seq.frefindex

use set.int

use printfunc

use standard

use seq.symbol

use symbol2

use wasm

use encoding.wfunc

use otherseq.wfunc

use process.seq.word

use encoding.word5

use seq.word5

use words

use encoding.wtype

use seq.wtype

Function =(a:wtype, b:wtype) boolean val.a = val.b

function hash(a:wtype) int
hash.for acc = empty:seq.int, @e ∈ val.a do acc + toint.@e /do acc

Export type:wtype

type wtype is val:seq.byte

Function asbytes(a:wtype) seq.byte val.a

Function asset(a:wtype) set.int asset.[toint.first.val.a]

Function wtype(b:byte) wtype wtype.[b]

Function void wtype wtype.tobyte.0x40

Function f64 wtype wtype.tobyte.0x7C

Function f32 wtype wtype.tobyte.0x7D

Function i64 wtype wtype.tobyte.0x7E

Function i32 wtype wtype.tobyte.0x7F

Function %(w:wtype) seq.word
if w = void then
 "void"
else if w = i64 then
 "i64"
else if w = f64 then
 "f64"
else if w = i32 then
 "i32"
else if length.val.w = 1 then
 %.first.val.w
else
 let nopara = toint.(val.w)_2,
 for acc = "func (", e ∈ subseq(val.w, 3, nopara + 2) do
  acc + %.wtype.e
 /do
  acc + ")" + if (val.w)_(nopara + 3) = tobyte.1 then %.wtype.last.val.w else "void"

Function printtypeidx(i:int) seq.word
%.decode.to:encoding.wtype(i + 1) + "(idx:$(i))"

Function typeindex(paras:seq.wtype, rt:wtype) int
addorder.wtype([tobyte.0x60] + LEBu.length.paras
+ for acc = empty:seq.byte, @e ∈ paras do acc + val.@e /do acc /for
+ LEBu.1
+ val.rt)
- 1

Function towtypelist(i:int) seq.wtype
let val = val.decode.to:encoding.wtype(i + 1)
assert val_1 = tobyte.0x60 report "type problem",
for acc = empty:seq.wtype, b ∈ subseq(val, 3, length.val - 2) + last.val do
 acc + wtype.b
/do acc

Function typeindex(paras:seq.wtype) int
addorder.wtype([tobyte.0x60] + LEBu.length.paras
+ for acc = empty:seq.byte, @e ∈ paras do acc + val.@e /do acc /for
+ LEBu.0)
- 1

function %(f:wfunc) seq.word
let p = process.printfunc.f,
if aborted.p then message.p else result.p

Function createwasm(imports:seq.seq.byte
 , exports:seq.seq.byte
 , data:seq.int
 , startidx:int
 , fn:filename
 , info:boolean) seq.file
let eledata = elementdata
let tmp1 = sort.encodingdata:wfunc
let importfuncs = subseq(tmp1, 1, length.imports)
let funcswithcode = tmp1 << length.imports,
for code = empty:seq.seq.byte, funcs = empty:seq.seq.byte, p ∈ funcswithcode do
 next(code + code.p, funcs + LEBu.typeidx.p)
/do
 let initmemorysize = (length.data + 2^13 - 1) / 2^13
 {assert false report" XX"+toword.((length.data+2^16-1) / 2^16)}
 let magic = 
  [tobyte.0x00, tobyte.0x61, tobyte.0x73, tobyte.0x6D, tobyte.1
   , tobyte.0, tobyte.0, tobyte.0]
 let te = encodingdata:wtype
 let types = for acc = LEBu.length.te, @e ∈ te do acc + val.@e /do acc
 let beforecode = 
  magic + tobyte.1 + vector.types + tobyte.2 + vector.vector.imports + tobyte.3
  + vector.vector.funcs
  + {tables} tobyte.4
  + vector.vector.[[tobyte.0x70, tobyte.0x00] + LEBu(length.eledata + 2)]
  + {memory} tobyte.5
  + vector.vector.[[tobyte.0, tobyte.initmemorysize]]
  + tobyte.7
  + vector.vector.exports
  + {start} tobyte.8
  + vector.LEBu.startidx
  + {elements} tobyte.9
  + vector.vector.[
   [tobyte.0, i32const] + LEBs.2 + END
   + vector.for frefs = empty:seq.seq.byte, f ∈ eledata do frefs + LEBu.f /do frefs]
 let codevector = vector.code
 let forlater = 
  for txt = "Successful compile /p", p2 ∈ importfuncs do
   txt + %.p2 + "typeidx =" + printtypeidx.typeidx.p2 + "/br"
  /do txt /for
  + for txt = "", cnt = 2, f ∈ eledata do
   next(txt + "$(cnt):$(f)", cnt + 1)
  /do "tableelements $(txt) /p" /for
  + for txt = ""
   , offset = length.beforecode + length.LEBu.length.codevector + 1
   , p2 ∈ funcswithcode
  do
   next(
    txt + %.tobits.offset + %.sym.p2
    + "funcidx = $(funcidx.p2) typidx = $(printtypeidx.typeidx.p2) /p"
    + %.p2
    + "/p"
    , offset + length.LEBu.length.code.p2 + length.code.p2)
  /do txt
 let total = 
  beforecode + {code} tobyte.10 + vector.codevector + {data} tobyte.11
  + vector.vector.[
   [tobyte.0, i32const] + LEBs.0 + END
   + vector.for acc = empty:seq.byte, val ∈ data do
    for acc2 = acc, @i = 1, @e ∈ constantseq(8, 0) do
     next(acc2 + tobyte(bits.val >> (8 * @i - 8) ∧ bits.255), @i + 1)
    /do acc2
   /do acc]
 ,
 if info then
  [file(fn, total)
   , file(filename("+$(dirpath.fn)" + merge([name.fn] + "info") + ".html"), forlater)]
 else
  [file(fn, total)]

Function funcbody(localtypes:seq.wtype, code:seq.byte) seq.byte
let b = 
 if isempty.localtypes then
  LEBu.0
 else
  for result = empty:seq.byte
   , count = 1
   , segcount = 1
   , last = first.localtypes
   , t ∈ localtypes << 1
  do
   if last = t then
    next(result, count + 1, segcount, t)
   else
    next(result + LEBu.count + val.last, 1, segcount + 1, t)
  /do LEBu.segcount + result + LEBu.count + val.last
,
vector(b + code + END)

type efuncidx is sym:symbol

Function =(a:efuncidx, b:efuncidx) boolean sym.a = sym.b

Function hash(a:efuncidx) int hash.sym.a

Function nobodies(i:int) seq.symbol
let x = encodingdata:efuncidx,
for acc = empty:seq.symbol, j ∈ arithseq(length.x - i + 1, 1, i) do
 let sym = sym.decode.to:encoding.efuncidx(j),
 if isempty.findencode.wfunc(sym, empty:seq.byte, 0, 0) then acc + sym else acc
/do acc

Function funcidx(sym:symbol) int value.funcidx(addorder.efuncidx.sym - 1)

type funcidx is value:int

type wfunc is sym:symbol, code:seq.byte, funcidx:int, typeidx:int

Export type:wfunc

Export sym(wfunc) symbol

Export code(wfunc) seq.byte

Export funcidx(wfunc) int

Export typeidx(wfunc) int

Function wfunc(alltypes:typedict, sym:symbol, code:seq.byte) wfunc
wfunc(alltypes, sym, code,-1)

Function =(a:wfunc, b:wfunc) boolean sym.a = sym.b

Function hash(a:wfunc) int hash.sym.a

Function >1(a:wfunc, b:wfunc) ordering funcidx.a >1 funcidx.b

Function lookup2(s:seq.wfunc, a:wfunc) seq.wfunc
let t = 
 for found = empty:seq.wfunc, e ∈ s
 while isempty.found
 do
  if a = e then found + e else found
 /do found
assert name.sym.a ∉ "intpart" ∨ not.isempty.t
report
 "KKK $(sym.a)
  $(for txt = ">>>", b ∈ s do txt + %.sym.b + "/br" /do txt)
  "
,
t

Function wfunc(alltypes:typedict, sym:symbol, code:seq.byte, funcidx:int) wfunc
wfunc(sym
 , code
 , funcidx
 , if inmodule(sym, "core32") then typeidx32(alltypes, sym) else typeidx64(alltypes, sym))

Function inmodule(sym:symbol, modname:seq.word) boolean name.module.sym ∈ modname

function typeidx32(alltypes:typedict, sym:symbol) int
if wordname.sym = "initwords3"_1 then
 typeindex.empty:seq.wtype
else
 typeindex(for acc = empty:seq.wtype, @e ∈ paratypes.sym do acc + wtype32(alltypes, @e) /do acc
  , wtype32(alltypes, resulttype.sym))

Function typeidx64(alltypes:typedict, sym:symbol) int
if wordname.sym = "initwords3"_1 then
 typeindex.empty:seq.wtype
else
 typeindex(for acc = empty:seq.wtype, @e ∈ paratypes.sym do acc + wtype64(alltypes, @e) /do acc
  , wtype64(alltypes, resulttype.sym))

Function wtype64(alltypes:typedict, typ:mytype) wtype
let kind = basetype(typ, alltypes),
if kind = typeboolean then i32 else if kind = typereal then f64 else i64

Function wtype32(alltypes:typedict, typ:mytype) wtype
let kind = basetype(typ, alltypes),
if kind = typeboolean ∨ kind = typeptr then
 i32
else if kind = typereal then f64 else i64

Function addf(alltypes:typedict, sym:symbol, b:seq.byte) int
addorder.wfunc(alltypes, sym, b, funcidx.sym)

Function funcidx2typedesc(arg:int) seq.word
for acc = "", p ∈ encodingdata:wfunc
while acc = ""
do
 if funcidx.p = arg then
  let xx = printtypeidx.typeidx.p >> 5
  assert not.isempty.xx report "KLJ $(printtypeidx.typeidx.p)",
  xx
 else
  acc
/do acc

Function Wcall(sym:symbol) seq.byte [call] + LEBu.funcidx.sym

Function globalspace int
{???? needs adjustment}
let t = 25 * 24
assert t mod 8 = 0 report "globalspace must be multiple of 8",
t

____________________

type word5 is chars:seq.char

Function =(a:word5, b:word5) boolean chars.a = chars.b

Function hash(a:word5) int hash.chars.a

Function wordconst(w:word) symbol Lit.valueofencoding.encode.word5.decodeword.w

Function wordsconst(s:seq.word) symbol
for acc = empty:seq.symbol, w ∈ s do
 acc + wordconst.w
/do Constant2(acc + Sequence(seqof.typeint, length.acc))

Function initialwordconst symbol
for acc2 = empty:seq.symbol, p ∈ encodingdata:word5 do
 for acc = empty:seq.symbol, c ∈ chars.p do
  acc + Lit.toint.c
 /do acc2 + Constant2(acc + Sequence(seqof.typeint, length.acc))
/do Constant2(acc2 + Sequence(seqof.seqof.typeint, length.acc2))

________________

type frefindex is toint:int

Function hash(a:frefindex) int toint.a + 1

Function =(a:frefindex, b:frefindex) boolean toint.a = toint.b

Function elementdata seq.int
for acc = empty:seq.int, p ∈ encodingdata:frefindex do acc + toint.p /do acc

Export type:frefindex

Function tableindex(sym:symbol) int addorder.frefindex.funcidx.sym + 1

Function funcidx2symbol(idx:int) symbol sym.decode.to:encoding.efuncidx(idx)

________________

Function startencodings int
length.encodingdata:efuncidx + length.encodingdata:wfunc + length.encodingdata:word5
+ length.encodingdata:datax
+ length.encodingdata:frefindex

type datax is globalname:word, elements:seq.int

Export type:datax

Function hash(a:datax) int
if globalname.a ∉ "." then hash.globalname.a else hash.elements.a

Function =(a:datax, b:datax) boolean
if globalname.a ∉ "." ∨ globalname.b ∉ "." then
 globalname.a = globalname.b
else
 elements.a = elements.b

Function dataseg seq.int
for acc = constantseq(globalspace / 8, 0), p ∈ encodingdata:datax do
 acc + elements.p
/do acc

Function allocateconstspace(globalname:word, elements:seq.int) int
let k = addorder.datax(globalname, elements),
for offset = globalspace, p ∈ subseq(encodingdata:datax, 1, k - 1) do
 offset + 8 * length.elements.p
/do offset

/Function constintseq (elements:seq.int) int allocateconstspace ("."_1, [0, length.elements]+

function constantcode(s:symbol) seq.symbol
let code1 = fullconstantcode.s,
if isSequence.last.code1 then
 [Lit.0, Lit.nopara.last.code1] + code1 >> 1
else
 code1 >> 1

Function getoffset(const:symbol) int
let elements = 
 for elements = empty:seq.int, sym ∈ constantcode.const do
  elements
  + if inmodule(sym, "$real") ∨ inmodule(sym, "$int") ∨ inmodule(sym, "$boolean") then
   value.sym
  else if sym = Littrue then
   1
  else if sym = Litfalse then
   0
  else if isFref.sym then
   tableindex.basesym.sym
  else if iswordseq.sym then
   getoffset.wordsconst.worddata.sym
  else if isword.sym then
   value.wordconst.wordname.sym
  else
   assert isrecordconstant.sym report "problem getoffset $(sym)",
   getoffset.sym
 /do elements
,
allocateconstspace("."_1, elements) 