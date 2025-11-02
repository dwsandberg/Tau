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

use symbol1

use wasm

use encoding.wfunc

use seq1.wfunc

use sort.wfunc

use word

use process.seq.word

use encoding.word5

use seq.word5

use encoding.wtype

use seq.wtype

Function =(a:wtype, b:wtype) boolean val.a = val.b

function hash(a:wtype) int
for acc = empty:seq.int, @e ∈ val.a do acc + toint.@e,
hash.acc

Export type:wtype

type wtype is val:seq.byte

Function asbytes(a:wtype) seq.byte val.a

Function asset(a:wtype) set.int asset.[toint.(val.a) sub 1]

Function wtype(b:byte) wtype wtype.[b]

Function void wtype wtype.tobyte.0x40

Function f64 wtype wtype.tobyte.0x7C

Function f32 wtype wtype.tobyte.0x7D

Function i64 wtype wtype.tobyte.0x7E

Function i32 wtype wtype.tobyte.0x7F

Function %(w:wtype) seq.word
if w = void then "void"
else if w = i64 then "i64"
else if w = f64 then "f64"
else if w = i32 then "i32"
else if n.val.w = 1 then %.(val.w) sub 1
else
 let nopara = toint.(val.w) sub 2
 for acc = "func (", e ∈ subseq(val.w, 3, nopara + 2)
 do acc + %.wtype.e,
 acc
  + ")"
  + if (val.w) sub (nopara + 3) = tobyte.1 then %.wtype.last.val.w else "void"

Function printtypeidx(i:int) seq.word
%.decode.to:encoding.wtype(i + 1) + "(idx::(i))"

Function typeindex(paras:seq.wtype, rt:wtype) int
addorder.wtype(
 [tobyte.0x60]
  + LEBu.n.paras
  + for acc = empty:seq.byte, @e ∈ paras do acc + val.@e,
 acc + LEBu.1 + val.rt
)
 - 1

Function towtypelist(i:int) seq.wtype
let val = val.decode.to:encoding.wtype(i + 1)
assert val sub 1 = tobyte.0x60 report "type problem"
for acc = empty:seq.wtype, b ∈ subseq(val, 3, n.val - 2) + last.val
do acc + wtype.b,
acc

Function typeindex(paras:seq.wtype) int
addorder.wtype(
 [tobyte.0x60]
  + LEBu.n.paras
  + for acc = empty:seq.byte, @e ∈ paras do acc + val.@e,
 acc + LEBu.0
)
 - 1

function %(f:wfunc) seq.word
let p = process.printfunc.f,
if aborted.p then message.p else result.p

Function createwasm(
imports:seq.seq.byte
, exports:seq.seq.byte
, data:seq.int
, startidx:int
, fn:filename
, info:boolean
) seq.file
let eledata = elementdata
let tmp1 = sort.encodingdata:wfunc
let importfuncs = subseq(tmp1, 1, n.imports)
let funcswithcode = tmp1 << n.imports
for code = empty:seq.seq.byte, funcs = empty:seq.seq.byte, p ∈ funcswithcode
do next(code + code.p, funcs + LEBu.typeidx.p)
let initmemorysize = (n.data + 2 sup 13 - 1) / 2 sup 13
let magic = [tobyte.0x00, tobyte.0x61, tobyte.0x73, tobyte.0x6D, tobyte.1, tobyte.0, tobyte.0, tobyte.0]
let te = encodingdata:wtype
let types =
 for acc = LEBu.n.te, @e ∈ te do acc + val.@e,
 acc
let beforecode =
 magic
  + tobyte.1
  + vector.types
  + tobyte.2
  + vector.vector.imports
  + tobyte.3
  + vector.vector.funcs
  + {tables} tobyte.4
  + vector.vector.[[tobyte.0x70, tobyte.0x00] + LEBu(n.eledata + 2)]
  + {memory} tobyte.5
  + vector.vector.[[tobyte.0, tobyte.initmemorysize]]
  + tobyte.7
  + vector.vector.exports
  + {start} tobyte.8
  + vector.LEBu.startidx
  + {elements} tobyte.9
  + vector.vector.[
  [tobyte.0, i32const]
   + LEBs.2
   + END
   + vector(
   for frefs = empty:seq.seq.byte, f ∈ eledata
   do frefs + LEBu.f,
   frefs
  )
 ]
let codevector = vector.code
let forlater =
 [
  for
   txt = "Successful compile
   /p"
   , p2 ∈ importfuncs
  do txt + %.p2 + "typeidx =" + printtypeidx.typeidx.p2 + "/br",
  txt
  , for txt = "", cnt = 2, f ∈ eledata
  do next(txt + (%.cnt + ":" + %.f), cnt + 1),
  "tableelements:(txt) /p"
  , for txt = "", offset = n.beforecode + n.LEBu.n.codevector + 1, p2 ∈ funcswithcode
  do
   next(
    txt
     + %.tobits.offset
     + %.sym.p2
     + "funcidx =:(funcidx.p2) typidx =:(printtypeidx.typeidx.p2) /p"
     + %.p2
     + "/p"
    , offset + n.LEBu.n.code.p2 + n.code.p2
   ),
  txt
 ]
let total =
 beforecode
  + {code} tobyte.10
  + vector.codevector
  + {data} tobyte.11
  + vector.vector.[
  [tobyte.0, i32const]
   + LEBs.0
   + END
   + vector(
   for acc = empty:seq.byte, val ∈ data
   do
    for acc2 = acc, @i = 1, @e ∈ constantseq(8, 0)
    do next(acc2 + tobyte(bits.val >> (8 * @i - 8) ∧ bits.255), @i + 1),
    acc2,
   acc
  )
 ],
if info then
 [
  file(fn, total)
  , file(
   filename("+:(dirpath.fn)" + merge([name.fn] + "info") + ".html")
   , forlater sub 1 + forlater sub 2 + forlater sub 3
  )
 ]
else [file(fn, total)]

Function funcbody(localtypes:seq.wtype, code:seq.byte) seq.byte
let b =
 if isempty.localtypes then LEBu.0
 else
  for
   result = empty:seq.byte
   , count = 1
   , segcount = 1
   , last = localtypes sub 1
   , t ∈ localtypes << 1
  do
   if last = t then next(result, count + 1, segcount, t)
   else next(result + LEBu.count + val.last, 1, segcount + 1, t),
  LEBu.segcount + result + LEBu.count + val.last,
vector(b + code + END)

type efuncidx is sym:symbol

Function =(a:efuncidx, b:efuncidx) boolean sym.a = sym.b

Function hash(a:efuncidx) int hash.sym.a

Function nobodies(i:int) seq.symbol
let x = encodingdata:efuncidx
for acc = empty:seq.symbol, j ∈ arithseq(n.x - i + 1, 1, i)
do
 let sym = sym.decode.to:encoding.efuncidx(j),
 if isempty.findencode.wfunc(sym, empty:seq.byte, 0, 0) then acc + sym else acc,
acc

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
 do if a = e then found + e else found,
 found
assert name.sym.a ∉ "intpart" ∨ not.isempty.t report
 "KKK:(sym.a):(for txt = ">>>", b ∈ s do txt + %.sym.b + "/br",
 txt)",
t

Function wfunc(alltypes:typedict, sym:symbol, code:seq.byte, funcidx:int) wfunc
wfunc(
 sym
 , code
 , funcidx
 , if name.module.sym ∈ "core32" then typeidx32(alltypes, sym)
 else typeidx64(alltypes, sym)
)

function typeidx32(alltypes:typedict, sym:symbol) int
if wordname.sym = "initwords3" sub 1 then typeindex.empty:seq.wtype
else
 typeindex(
  for acc = empty:seq.wtype, @e ∈ paratypes.sym
  do acc + wtype32(alltypes, @e),
  acc
  , wtype32(alltypes, resulttype.sym)
 )

Function typeidx64(alltypes:typedict, sym:symbol) int
if wordname.sym = "initwords3" sub 1 then typeindex.empty:seq.wtype
else
 typeindex(
  for acc = empty:seq.wtype, @e ∈ paratypes.sym
  do acc + wtype64(alltypes, @e),
  acc
  , wtype64(alltypes, resulttype.sym)
 )

Function wtype64(alltypes:typedict, typ:mytype) wtype
let kind = basetype(typ, alltypes),
if kind = typeboolean then i32 else if kind = typereal then f64 else i64

Function wtype32(alltypes:typedict, typ:mytype) wtype
let kind = basetype(typ, alltypes),
if kind = typeboolean ∨ kind = typeptr then i32 else if kind = typereal then f64 else i64

Function addf(alltypes:typedict, sym:symbol, b:seq.byte) int
addorder.wfunc(alltypes, sym, b, funcidx.sym)

Function funcidx2typedesc(arg:int) seq.word
for acc = "", p ∈ encodingdata:wfunc
while acc = ""
do
 if funcidx.p = arg then
  let xx = printtypeidx.typeidx.p >> 5
  assert not.isempty.xx report "KLJ:(printtypeidx.typeidx.p)",
  xx
 else acc,
acc

Function Wcall(sym:symbol) seq.byte [call] + LEBu.funcidx.sym

Function globalspace int
{???? needs adjustment}
let t = 25 * 24
assert t mod 8 = 0 report "globalspace must be multiple of 8",
t

-------------------------------

type word5 is chars:seq.char

Function =(a:word5, b:word5) boolean chars.a = chars.b

Function hash(a:word5) int hash.chars.a

Function wordconst(w:word) symbol Lit.valueofencoding.encode.word5.decodeword.w

Function initialwordconst(libname:word) symbol
for acc2 = empty:seq.symbol, p ∈ encodingdata:word5
do
 for acc = empty:seq.symbol, c ∈ chars.p
 do acc + Lit.toint.c,
 acc2 + Constant2(libname, acc + Sequence(seqof.typeint, n.acc)),
Constant2(libname, acc2 + Sequence(seqof.seqof.typeint, n.acc2))

-------------------------------

type frefindex is toint:int

Function hash(a:frefindex) int toint.a + 1

Function =(a:frefindex, b:frefindex) boolean toint.a = toint.b

Function elementdata seq.int
for acc = empty:seq.int, p ∈ encodingdata:frefindex
do acc + toint.p,
acc

Export type:frefindex

Function tableindex(sym:symbol) int addorder.frefindex.funcidx.sym + 1

Function funcidx2symbol(idx:int) symbol sym.decode.to:encoding.efuncidx(idx)

-------------------------------

Function startencodings int
n.encodingdata:efuncidx
 + n.encodingdata:wfunc
 + n.encodingdata:word5
 + n.encodingdata:datax
 + n.encodingdata:frefindex

type datax is globalname:word, elements:seq.int

Export type:datax

Function hash(a:datax) int
if globalname.a ∉ "." then hash.globalname.a else hash.elements.a

Function =(a:datax, b:datax) boolean
if globalname.a ∉ "." ∨ globalname.b ∉ "." then globalname.a = globalname.b
else elements.a = elements.b

Function dataseg seq.int
for acc = constantseq(globalspace / 8, 0), p ∈ encodingdata:datax
do acc + elements.p,
acc

Function allocateconstspace(globalname:word, elements:seq.int) int
let k = addorder.datax(globalname, elements)
for offset = globalspace, p ∈ subseq(encodingdata:datax, 1, k - 1)
do offset + 8 * n.elements.p,
offset

Function getoffset(s:seq.word, libname:word) int
for acc = empty:seq.symbol, w ∈ s do acc + wordconst.w,
getoffset(Constant2(libname, acc + Sequence(seqof.typeint, n.acc)), libname)

Function getoffset(const:symbol, libname:word) int
let code1 = fullconstantcode.const
let start = if kind.last.code1 = ksequence then [0, nopara.last.code1] else empty:seq.int
for elements = start, sym ∈ code1 >> 1
do
 let kind = kind.sym,
 elements
  + if kind ∈ [kreal, kint] then value.sym
 else if kind = ktrue then 1
 else if kind = kfalse then 0
 else if kind = kfref then tableindex.basesym.sym
 else if kind = kwords then getoffset(worddata.sym, libname)
 else if kind = kword then value.wordconst.wordname.sym
 else
  assert kind = kconstantrecord report "problem getoffset:(sym)",
  getoffset(sym, libname),
allocateconstspace("." sub 1, elements) 
