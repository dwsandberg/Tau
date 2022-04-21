
Module funcidx

use UTF8

use bits

use standard

use symbol2

use tausupport

use wasm

use wasmconstant

use words

use seq.byte

use encoding.datax

use encoding.efuncidx

use encoding.frefindex

use set.int

use seq.symbol

use encoding.wfunc

use seq.wfunc

use otherseq.word

use sparseseq.word

use stack.word

use encoding.word5

use encoding.wtype

use seq.wtype

use seq.seq.byte

use seq.encodingpair.datax

use seq.encodingpair.efuncidx

use seq.encodingpair.frefindex

use seq.encodingpair.wfunc

use seq.encodingpair.word5

use seq.encodingpair.wtype

Function funcidx2sym(i:int)symbol sym.decode.to:encoding.efuncidx(i + 1)

Function =(a:wtype, b:wtype)boolean val.a = val.b

function assignencoding(a:wtype)int nextencoding.a

function hash(a:wtype)int hash.for acc = empty:seq.int, @e ∈ val.a do acc + toint.@e /for(acc)

Export type:wtype

type wtype is val:seq.byte

Function asbytes(a:wtype)seq.byte val.a

Function asset(a:wtype)set.int asset.[toint.first.val.a]

Function wtype(b:byte)wtype wtype.[b]

Function void wtype wtype.tobyte.0x40

Function f64 wtype wtype.tobyte.0x7C

Function f32 wtype wtype.tobyte.0x7D

Function i64 wtype wtype.tobyte.0x7E

Function i32 wtype wtype.tobyte.0x7F

Function print(w:wtype)seq.word
if w = void then"void"
else if w = i64 then"i64"
else if w = f64 then"f64"
else if w = i32 then"i32"
else if length.val.w = 1 then print.first.val.w
else
 let nopara = toint.(val.w)_2
 for acc = "func(", e ∈ subseq(val.w, 3, nopara + 2)do acc + print.wtype.e /for(acc + ")"
 + if(val.w)_(nopara + 3) = tobyte.1 then print.wtype.last.val.w else"void"/if)

Function printtypeidx(i:int)seq.word print.decode.to:encoding.wtype(i + 1) + "(idx:" + print.i + ")"

Function typeindex(paras:seq.wtype, rt:wtype)int
valueofencoding.encode.wtype([tobyte.0x60] + LEBu.length.paras
+ for acc = empty:seq.byte, @e ∈ paras do acc + val.@e /for(acc)
+ LEBu.1
+ val.rt)
- 1

Function typeindex(alltypes:typedict, sym:symbol)int
typeindex(for acc = empty:seq.wtype, @e ∈ paratypes.sym do acc + wtype64(alltypes, @e)/for(acc)
, wtype64(alltypes, resulttype.sym)
)

Function towtypelist(i:int)seq.wtype
let val = val.decode.to:encoding.wtype(i + 1)
assert val_1 = tobyte.0x60 report"type problem"
for acc = empty:seq.wtype, b ∈ subseq(val, 3, length.val - 2) + last.val do acc + wtype.b /for(acc)

Function typeindex(paras:seq.wtype)int
valueofencoding.encode.wtype([tobyte.0x60] + LEBu.length.paras
+ for acc = empty:seq.byte, @e ∈ paras do acc + val.@e /for(acc)
+ LEBu.0)
- 1

Function createwasm(imports:seq.seq.byte
, funcs:seq.seq.byte
, exports:seq.seq.byte
, code:seq.seq.byte
, data:seq.int
, funcrefs:seq.int
, startidx:int
)seq.byte
let initmemorysize = (length.data + 2^13 - 1) / 2^13
{assert false report"XX"+toword.((length.data+2^16-1)/ 2^16)}
let magic = [tobyte.0x00, tobyte.0x61, tobyte.0x73, tobyte.0x6D, tobyte.1, tobyte.0, tobyte.0, tobyte.0]
let te = encoding:seq.encodingpair.wtype
let types = for acc = LEBu.length.te, @e ∈ te do acc + val.data.@e /for(acc)
magic + [tobyte.1] + LEBu.length.types + types + tobyte.2 + vector.vector.imports + tobyte.3
+ vector.vector.funcs
+ {tables}tobyte.4
+ vector.vector.[[tobyte.0x70, tobyte.0x00] + LEBu(length.funcrefs + 2)]
+ {memory}tobyte.5
+ vector.vector.[[tobyte.0, tobyte.initmemorysize]]
+ tobyte.7
+ vector.vector.exports
+ {start}tobyte.8
+ vector.LEBu.startidx
+ {elements}tobyte.9
+ vector.vector.[[tobyte.0, i32const] + LEBs.2 + END
+ vector.for frefs = empty:seq.seq.byte, f ∈ funcrefs do frefs + LEBu.f /for(frefs)
]
+ {code}tobyte.10
+ vector.vector.code
+ {data}tobyte.11
+ vector.vector.[[tobyte.0, i32const] + LEBs.0 + END
+ vector.for acc = empty:seq.byte, val ∈ data do
 for acc2 = acc, @i = 1, @e ∈ constantseq(8, 0)do next(acc2 + tobyte(bits.val >> (8 * @i - 8) ∧ bits.255), @i + 1)/for(acc2)
/for(acc)
]

Function funcbody(localtypes:seq.wtype, code:seq.byte)seq.byte
let locals = 
 if isempty.localtypes then empty:seq.seq.byte else localtypes(localtypes, 2, 1, empty:seq.seq.byte)
let b = for acc = LEBu.length.locals, @e ∈ locals do acc + @e /for(acc)
vector(b + code + END)

function localtypes(s:seq.wtype, i:int, count:int, result:seq.seq.byte)seq.seq.byte
if i > length.s then result + [LEBu.count + val.s_(i - 1)]
else if s_(i - 1) = s_i then localtypes(s, i + 1, count + 1, result)
else localtypes(s, i + 1, 1, result + [LEBu.count + val.s_(i - 1)])

type efuncidx is sym:symbol

Function =(a:efuncidx, b:efuncidx)boolean sym.a = sym.b

Function hash(a:efuncidx)int hash.sym.a

Function assignencoding(a:efuncidx)int nextencoding.a

Function printefuncidx seq.word
for txt = "", x ∈ encoding:seq.encodingpair.efuncidx do txt + toword(valueofencoding.code.x - 1) + print.sym.data.x + EOL /for(txt)

Function nobodies(i:int)seq.symbol
let x = encoding:seq.encodingpair.efuncidx
for acc = empty:seq.symbol, j ∈ arithseq(length.x - i + 1, 1, i)do
 let sym = sym.decode.to:encoding.efuncidx(j)
 if isempty.findencode.wfunc(sym, empty:seq.byte, 0, 0)then acc + sym else acc
/for(acc)

Function funcidx(sym:symbol)int value.funcidx(valueofencoding.encode.efuncidx.sym - 1)

type funcidx is value:int

type wfunc is sym:symbol, code:seq.byte, funcidx:int, typeidx:int

Export type:wfunc

Export sym(wfunc)symbol

Export code(wfunc)seq.byte

Export funcidx(wfunc)int

Export typeidx(wfunc)int

Function wfunc(alltypes:typedict, sym:symbol, code:seq.byte)wfunc wfunc(alltypes, sym, code, -1)

Function =(a:wfunc, b:wfunc)boolean sym.a = sym.b

Function hash(a:wfunc)int hash.sym.a

Function assignencoding(a:wfunc)int nextencoding.a

Function ?(a:encodingpair.wfunc, b:encodingpair.wfunc)ordering funcidx.data.a ? funcidx.data.b

Function lookup2(s:seq.wfunc, a:wfunc)seq.wfunc
let t = 
 for found = empty:seq.wfunc, e ∈ s while isempty.found do if a = e then found + e else found /for(found)
assert name.sym.a ∉ "intpart" ∨ not.isempty.t
report"KKK" + print.sym.a
+ for txt = ">>>", b ∈ s do txt + print.sym.b + EOL /for(txt)
t

Function wfunc(alltypes:typedict, sym:symbol, code:seq.byte, funcidx:int)wfunc
wfunc(sym
, code
, funcidx
, if inmodule(sym, "core32")then typeidx32(alltypes, sym)
else typeidx64(alltypes, sym)
)

Function inmodule(sym:symbol, modname:seq.word)boolean name.module.sym ∈ modname

Function typeidx32(alltypes:typedict, sym:symbol)int
if wordname.sym = "initwords3"_1 then typeindex.empty:seq.wtype
else
 typeindex(for acc = empty:seq.wtype, @e ∈ paratypes.sym do acc + wtype32(alltypes, @e)/for(acc)
 , wtype32(alltypes, resulttype.sym)
 )

Function typeidx64(alltypes:typedict, sym:symbol)int
if wordname.sym = "initwords3"_1 then typeindex.empty:seq.wtype
else
 typeindex(for acc = empty:seq.wtype, @e ∈ paratypes.sym do acc + wtype64(alltypes, @e)/for(acc)
 , wtype64(alltypes, resulttype.sym)
 )

Function wtype64(alltypes:typedict, typ:mytype)wtype
let kind = basetype(typ, alltypes)
if kind = typeboolean then i32 else if kind = typereal then f64 else i64

Function wtype32(alltypes:typedict, typ:mytype)wtype
let kind = basetype(typ, alltypes)
if kind = typeboolean ∨ kind = typeptr then i32
else if kind = typereal then f64 else i64

Function addf(alltypes:typedict, sym:symbol, b:seq.byte)int
valueofencoding.encode.wfunc(alltypes, sym, b, funcidx.sym)

Function funcidx2typedesc(arg:int)seq.word
for acc = "", p ∈ encoding:seq.encodingpair.wfunc
while acc = ""
do if funcidx.data.p = arg then
 let xx = printtypeidx.typeidx.data.p >> 5
 assert not.isempty.xx report"KLJ" + printtypeidx.typeidx.data.p
 xx
else acc
/for({assert not.isempty.acc report"JKLSDF"+for txt="", q=encoding:seq.encodingpair.wfunc do txt+toword.funcidx.
data.q /for(txt)}
acc)

Function startencodings0 int length.encoding:seq.encodingpair.efuncidx + length.encoding:seq.encodingpair.wfunc

Function Wcall(sym:symbol)seq.byte[call] + LEBu.funcidx.sym

Function globalspace int
let t = 208
assert t mod 8 = 0 report"globalspace must be multiple of 8"
t

____________________

type word5 is toword:word

function assignencoding(a:word5)int encoding.toword.a

Function =(a:word5, b:word5)boolean toword.a = toword.b

Function hash(a:word5)int hash.toword.a

Export toword(word5)word

Export word5(word)word5

Export type:word5

Function wordconst(w:word)symbol
let discard = encode.word5.w
Lit.hash.w

Function wordsconst(s:seq.word)symbol
for acc = empty:seq.symbol, w ∈ s do acc + wordconst.w /for(Constant2(acc + Sequence(seqof.typeint, length.acc)))

Function initialwordpairlocations seq.int
for acc2 = empty:seq.int, p ∈ encoding:seq.encodingpair.word5 do
 let k = 
  for acc = empty:seq.symbol, c ∈ decodeword.toword.data.p do acc + Lit.toint.c /for(Constant2(acc + Sequence(seqof.typeint, length.acc)))
 acc2
 + getoffset.Constant2.[Lit.hash.toword.data.p
 , k
 , Lit.hash.decodeword.toword.data.p
 , Record.[typeint, typeint, typeint]
 ]
/for(acc2)

________________

type frefindex is toint:int

Function hash(a:frefindex)int toint.a + 1

Function =(a:frefindex, b:frefindex)boolean toint.a = toint.b

Function assignencoding(a:frefindex)int nextencoding.a

Function elementdata seq.int
for acc = empty:seq.int, p ∈ encoding:seq.encodingpair.frefindex do acc + toint.data.p /for(acc)

Export type:frefindex

Export toint(frefindex)int

Export frefindex(int)frefindex

Function tableindex(sym:symbol)int tableindex.funcidx.sym

Function tableindex(funcidx:int)int valueofencoding.encode.frefindex.funcidx + 1

________________

Function startencodings int
{length.encoding:seq.encodingpair.efuncidx+length.encoding:seq.encodingpair.wfunc+}startencodings0
+ length.encoding:seq.encodingpair.word5
+ length.encoding:seq.encodingpair.datax
+ length.encoding:seq.encodingpair.frefindex

type datax is no:word, elements:seq.int

Export type:datax

Function hash(a:datax)int hash.no.a

Function =(a:datax, b:datax)boolean no.a = no.b

Function assignencoding(a:datax)int
let p = encoding:seq.encodingpair.datax
if isempty.p then globalspace else valueofencoding.code.last.p + 8 * length.elements.data.last.p

Function dataseg seq.int
for acc = constantseq(globalspace / 8, 0), p ∈ encoding:seq.encodingpair.datax do acc + elements.data.p /for(acc)

Function allocateconstspace(no:word, elements:seq.int)int valueofencoding.encode.datax(no, elements)

Function constintseq(elements:seq.int)int
valueofencoding.encode.datax(toword.-nextencoding.datax("X"_1, [0]), [0, length.elements] + elements)

Function constbyteseq(a:seq.byte)int
let elements = 
 for elements = empty:seq.int, b ∈ packedbyteseqasbits.a do elements + toint.b /for(elements)
valueofencoding.encode.datax(toword.-nextencoding.datax("X"_1, [0]), elements)

Function getoffset(const:symbol)int
let elements = 
 for elements = empty:seq.int, sym ∈ constantcode.const do
  elements
  + if inmodule(sym, "$real") ∨ inmodule(sym, "$int")
  ∨ inmodule(sym, "$boolean")then
   value.sym
  else if sym = Littrue then 1
  else if sym = Litfalse then 0
  else if isFref.sym then tableindex.basesym.sym
  else if iswordseq.sym then getoffset.wordsconst.worddata.sym
  else if isword.sym then value.wordconst.wordname.sym
  else
   assert isrecordconstant.sym report"problem getoffset" + print.sym
   getoffset.sym
 /for(elements)
allocateconstspace((worddata.const)_1, elements)

Module wasmconstant

use standard

use symbol2

use seq.mytype

use seq.symbol

use seq.symdef

use set.symdef

use encoding.wasmconstant

use seq.encodingpair.wasmconstant

Function constantcode(s:symbol)seq.symbol
let code1 = fullconstantcode.s
if isSequence.last.code1 then[Lit.0, Lit.nopara.last.code1] + code1 >> 1 else code1 >> 1

Function fullconstantcode(s:symbol)seq.symbol
assert isrecordconstant.s report"constant code error" + print.s  
toseq.decode.to:encoding.wasmconstant(toint.name.s)

Function Constant2(args:seq.symbol, value:int)symbol symconst.valueofencoding.encode.wasmconstant(args, value)

Function Constant2(args:seq.symbol)symbol Constant2(args, 0)

Function hash(s:seq.symbol)int
hash.for acc = "", e ∈ s do acc + worddata.e + name.module.e /for(acc)

function assignencoding(a:wasmconstant)int
if value.a > 0 then value.a else valueofencoding.code.last.encoding:seq.encodingpair.wasmconstant + 1

Export type:wasmconstant

type wasmconstant is toseq:seq.symbol, value:int

function =(a:wasmconstant, b:wasmconstant)boolean toseq.a = toseq.b

function hash(a:wasmconstant)int hash.toseq.a

Function oldconstants(prg:set.symdef)int
{must have biggest val the last to be encoded}
for val = 0, max = first.toseq.prg, sd ∈ toseq.prg do
 if isrecordconstant.sym.sd then
  let thisval = toint.name.sym.sd
  if thisval < val then
   let discard = Constant2(code.sd, thisval)
   next(val, max)
  else if val = 0 then next(thisval, sd)
  else
   let discard = Constant2(code.max, val)
   next(thisval, sd)
 else next(val, max)
/for(let discard = Constant2(code.max, val)
0)

Function dumpvalues seq.word
for acc = "", p ∈ encoding:seq.encodingpair.wasmconstant do
 acc + toword.valueofencoding.code.p + toword.value.data.p + print.toseq.data.p + EOL
/for(acc) 