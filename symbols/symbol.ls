Module symbol

use UTF8

use bits

use mytype

use seq1.mytype

use standard

use seq.symbol

use set.symbol

use seq.symbolKind

use seq.typedef

use seq1.word

Export symbolKind(i:int) symbolKind

Export type:symbol

Export module(symbol) modref

Export types(symbol) seq.mytype

Export worddata(symbol) seq.word

Export type:symbolKind

Export toint(symbolKind) int

Export ∈(symbolKind, seq.symbolKind) boolean{From seq.symbolKind}

Export type:set.symbol{From set.symbol}

type symbol is worddata:seq.word, module:modref, types:seq.mytype, raw:bits, flags:bits

function maplibrary(libname:word, map:seq.word) word
let match = 1
let nomatch = 2
let done = 3
for state = 0, result = libname, x ∈ map
while state ≠ done
do
 if state = nomatch then next(0, result)
 else if state = match then next(done, x)
 else next(if x = libname then match else nomatch, result),
result

Function changelibrary(s:symbol, map:seq.word) symbol
for newtypes = empty:seq.mytype, t ∈ types.s do newtypes + changelibrary(t, map),
symbol(
 worddata.s
 , moduleref([maplibrary(library.module.s, map), name.module.s], para.module.s)
 , newtypes
 , raw.s
 , flags.s
)

Function replacestar(s:symbol, modulelib:word) symbol
symbol(
 worddata.s
 , moduleref(
  [if library.module.s ∈ "*" then modulelib else library.module.s, name.module.s]
  , para.module.s
 )
 , types.s
 , raw.s
 , flags.s
)

Function clearrequiresbit(s:symbol) symbol
{will clear requires bit}
let flags = flags.s ∧ (bits.-1 ⊻ requiresbit),
if flags = flags.s then s else symbol(worddata.s, module.s, types.s, raw.s, flags)

Function =(a:symbol, b:symbol) boolean
types.a >> 1 = types.b >> 1
 ∧ worddata.a = worddata.b
 ∧ module.a = module.b
 ∧ kind.a = kind.b

/Function same(a:symbol, b:symbol)boolean types.a = types.b ∧ worddata.a = worddata.b ∧ flags.a = flags.b ∧ raw.a = raw.b ∧ name.module.a = name.module.b ∧ para.module.a = para.module.b ∧ library.module.a = library.module.b

Function >1(a:symbol, b:symbol) ordering
a >2 b ∧ module.a >1 module.b ∧ toint.kind.a >1 toint.kind.b

Function >2(a:symbol, b:symbol) ordering
worddata.a >1 worddata.b
 ∧ types.a >> 1 >1 types.b >> 1
 ∧ issimplename.a >1 issimplename.b

Function privatefields(s:symbol) seq.int [toint.raw.s, toint.flags.s]

function unboundbit bits 0x80

function requiresbit bits 0x100

function tobits(kind:symbolKind) bits tobits.toint.kind

Function kind(s:symbol) symbolKind symbolKind.toint(flags.s ∧ mask(flagshift - 4))

Function issimplename(sym:symbol) boolean
kind.sym
 ∉ [kcompoundname, kbuiltincompound, kloop, kabortR, kabortI, kabortB, kabortP, kglobal]

Function isconst(s:symbolKind) boolean
s ∈ [kfref, kwords, kword, kint, kreal, kfalse, ktrue, kconstantrecord]

Function between(a:symbolKind, from:symbolKind, to:symbolKind) boolean
toint.a ≥ toint.from ∧ toint.a ≤ toint.to

Function isunbound(sym:symbol) boolean (flags.sym ∧ unboundbit) ≠ 0x0

Function hasrequires(sym:symbol) boolean (flags.sym ∧ requiresbit) ≠ 0x0

Function hash(sym:symbol) int hash(types.sym, worddata.sym)

Function setunbound(sym:symbol) symbol
symbol(worddata.sym, module.sym, types.sym, raw.sym, flags.sym ∨ unboundbit)

Function setrequires(sym:symbol) symbol
symbol(worddata.sym, module.sym, types.sym, raw.sym, flags.sym ∨ requiresbit)

Function replaceTsymbol(with:mytype, sym:symbol) symbol
let kind = kind.sym,
if with = typeT ∨ isconst.kind ∨ not(kind = kstart ∨ isAbstract.module.sym) then sym
else
 for newtypes = empty:seq.mytype, t ∈ types.sym do newtypes + replaceT(with, t)
 let newmodule = replaceT(with, module.sym),
 let newflags =
  if isAbstract.newmodule ∨ kind.sym ∈ [kcompoundname, kbuiltincompound] then flags.sym
  else tobits.symKind(newmodule, name.sym, newtypes >> 1, kind.sym) ∨ flags.sym ∧ 0xFFFC0,
 symbol(worddata.sym, newmodule, newtypes, raw.sym, newflags)

function symKind(
module:modref
, name:word
, paratypes:seq.mytype
, org:symbolKind
) symbolKind
if name.module ∈ "seq" then
 if name ∈ "∈" then kmember
 else if name ∈ "+" ∧ n.paratypes = 2 ∧ paratypes sub 1 = paratypes sub 2 then kcat
 else if name ∈ "sub" ∧ n.paratypes = 2 ∧ paratypes sub 2 = typeint then kidx
 else org
else if name.module = "internal" sub 1 then
 if name ∈ "not" then knot
 else if name ∈ "=" ∧ paratypes = [typeint, typeint] then keqlI
 else if name ∈ "=" ∧ paratypes = [typeboolean, typeboolean] then keqlB
 else if name ∈ "idxNB" then kidxNB
 else if name ∈ "getseqlength" then kgetseqlength
 else if name ∈ "getseqtype" then kgetseqtype
 else if name ∈ "stacktrace" then kstacktrace
 else if name ∈ "intpart" then kintpart
 else if name ∈ "casttoreal" then kcasttoreal
 else if name ∈ "toreal" then ktoreal
 else if name ∈ "toint" ∧ paratypes = [typebyte] then ktointbyte
 else if name ∈ "toint" ∧ paratypes = [typeint] then ktointbit
 else if name ∈ "representation" then krepresentation
 else if name ∈ "*" ∧ paratypes = [typereal, typereal] then kmulreal
 else if name ∈ "/" ∧ paratypes = [typereal, typereal] then kdivreal
 else if name ∈ "+" ∧ paratypes = [typereal, typereal] then kaddreal
 else if name ∈ "-" ∧ paratypes = [typereal, typereal] then ksubreal
 else if name ∈ ">1" ∧ paratypes = [typereal, typereal] then k>1real
 else if name ∈ "*" ∧ paratypes = [typeint, typeint] then kmulint
 else if name ∈ "/" ∧ paratypes = [typeint, typeint] then kdivint
 else if name ∈ "+" ∧ paratypes = [typeint, typeint] then kaddint
 else if name ∈ "-" ∧ paratypes = [typeint, typeint] then ksubint
 else if name ∈ ">1" ∧ paratypes = [typeint, typeint] then k>1int
 else if name ∈ ">" ∧ paratypes = [typeint, typeint] then kgrtI
 else if name ∈ "<<" ∧ paratypes = [typebits, typeint] then k<<bits
 else if name ∈ ">>" ∧ paratypes = [typebits, typeint] then k>>bits
 else if name ∈ "⊻" ∧ paratypes = [typebits, typebits] then kxorbits
 else if name ∈ "∨" ∧ paratypes = [typebits, typebits] then k∨bits
 else if name ∈ "∧" ∧ paratypes = [typebits, typebits] then k∧bits
 else if name ∈ "abort" ∧ paratypes = [typereal, seqof.typeword] then kabortR
 else if name ∈ "abort" ∧ paratypes = [typeint, seqof.typeword] then kabortI
 else if name ∈ "abort" ∧ paratypes = [typeboolean, seqof.typeword] then kabortB
 else if name ∈ "abort" ∧ paratypes = [typeptr, seqof.typeword] then kabortP
 else if name ∈ "set" ∧ paratypes = [typeptr, typeint] then ksetI
 else if name ∈ "set" ∧ paratypes = [typeptr, typereal] then ksetR
 else if name ∈ "set" ∧ paratypes = [typeptr, typeptr] then ksetP
 else if name ∈ "PreFref" then kprefref
 else kinternalmod
else if name.module ∈ "real" then
 if name ∈ "+" ∧ paratypes = [typereal, typereal] then kaddreal
 else if name ∈ "-" ∧ paratypes = [typereal, typereal] then ksubreal
 else if name ∈ "makereal" ∧ paratypes = [seqof.typeword] then kmakereal
 else org
else if name.module ∈ "builtin" then
 if name ∈ "fld" ∧ para.module ∈ [typeint, typeptr, typeboolean, typereal] then kfld
 else if name ∈ "createthreadZ" then kcreatethreadZ
 else kbuiltin
else org

Function symbol(module:modref, name:seq.word, paras:seq.mytype, rt:mytype) symbol
{OPTION COMPILETIME NOINLINE}
symbol(name, module, paras + rt, 0x0, tobits.symKind(module, name sub 1, paras, kother))

Function Br2(t:int, f:int) symbol
let raw = bits.t << 20 ∨ bits.f,
symbol(
 "BR2"
 , internalmod
 , [typeref.[toword.toint.raw, "." sub 1, "internallib" sub 1], type?]
 , bits.t << 20 ∨ bits.f
 , tobits.kbr
)

Function brt(s:symbol) int toint(raw.s >> 20 ∧ 0xFFFFF)

Function brf(s:symbol) int toint(raw.s ∧ 0xFFFFF)

Function type? mytype typeref."? internal internallib"

Function name(sym:symbol) word (worddata.sym) sub 1

Function value(sym:symbol) int toint.raw.sym

Function nopara(s:symbol) int
let kind = kind.s,
if isconst.kind ∨ kind = klocal then 0
else if kind ∈ [kdefine, kbr, kexit] then 1
else if kind ∈ [kcontinue, ksequence] then toint.name.s
else n.types.s - if issimplename.s then 1 else 2

function fsig2(name:word, nametype:seq.mytype, paratypes:seq.mytype) seq.word
let fullname = if isempty.nametype then [name] else [name] + ":" + %.nametype sub 1,
if n.paratypes = 0 then fullname
else
 for acc = fullname + "(", t ∈ paratypes do acc + %.t + ",",
 acc >> 1 + ")"

Function Record(types:seq.mytype) symbol
{reduce to basetype}
symbol("RECORD", moduleref("internallib othermod", typeptr), types + typeptr, 0x0, tobits.krecord)

Function Reallit(i:int) symbol
symbol([toword.i], othermod, [typereal], tobits.i, tobits.kreal)

Function Exit symbol symbol("EXITBLOCK", othermod, [type?], 0x0, tobits.kexit)

Function Start(t:mytype) symbol
{reduce to basetype}
symbol("Start", moduleref("internallib othermod", typeint), [t], 0x0, tobits.kstart)

Function EndBlock symbol symbol("BLOCK", othermod, [typeint], 0x0, tobits.kendblock)

Function symIdxNB(seqparatype:mytype) symbol
symbol(
 if isAbstract.seqparatype then builtinmod.seqparatype else internalmod
 , "idxNB"
 , [seqof.seqparatype, typeint]
 , seqparatype
)

Function NotOp symbol symbol(internalmod, "not", [typeboolean], typeboolean)

Function EqOp symbol symbol(internalmod, "=", [typeint, typeint], typeboolean)

Function GtOp symbol symbol(internalmod, ">", [typeint, typeint], typeboolean)

Function PlusOp symbol symbol(internalmod, "+", [typeint, typeint], typeint)

Function GetSeqLength symbol symbol(internalmod, "getseqlength", [typeptr], typeint)

Function GetSeqType symbol symbol(internalmod, "getseqtype", [typeptr], typeint)

Function PreFref symbol symbol(internalmod, "PreFref", empty:seq.mytype, typeptr)

Function deepcopySym(rt:mytype) symbol
if rt = typereal then symbol(moduleref."* tausupport", "deepcopy", [typereal], typereal)
else if rt = typeint then symbol(moduleref."* tausupport", "deepcopy", [typeint], typeint)
else symbol4(replaceT(parameter.rt, abstractModref.rt), "type" sub 1, rt, [rt], rt)

Function setSym(typ:mytype) symbol
let fldtype = if isseq.typ then typeptr else if isencoding.typ then typeint else typ,
symbol(
 if iscore4.fldtype then internalmod else builtinmod.fldtype
 , "set"
 , [typeptr, fldtype]
 , typeptr
)

Function Getfld(fldtype:mytype) symbol
let kind2 =
 if isseq.fldtype then typeptr
 else if isencoding.fldtype ∨ fldtype = typeword then typeint
 else fldtype,
symbol(builtinmod.kind2, "fld", [typeptr, typeint], kind2)

Function paratypes(s:symbol) seq.mytype
if kind.s = kfref then empty:seq.mytype
else if issimplename.s then types.s >> 1
else subseq(types.s, 2, n.types.s - 1)

Function resulttype(s:symbol) mytype
if kind.s = kfref then typeint else (types.s) sub n.types.s

Function fullname(s:symbol) seq.word
if issimplename.s then [name.s] else [name.s] + ":" + %.(types.s) sub 1

Function %(s:symbol) seq.word
let kind = kind.s,
if kind = klocal then %.merge(["%" sub 1] + wordname.s)
else if kind = kint then if value.s < 0 then "-:(-value.s)" else [name.s]
else if kind ∈ [kreal, kconstantrecord] then [name.s]
else if kind = kjmp then ":(name.s):(value.s)/br"
else if kind ∈ [kjmpB, klabel] then ":(name.s):(value.s)"
else if kind = kwords then if dq sub 1 ∈ worddata.s then "':(worddata.s)'" else dq.worddata.s
else if kind = kword then
 "WORD"
 + if wordname.s = encodeword.[char.254] then "word$char$254" sub 1
 else if wordname.s ∈ ("<* *> \keyword \br" + escapeformat) then encodeword(decodeword.wordname.s + char.32)
 else wordname.s
else if kind = kdefine then "Define:(name.s)"
else if kind = kcontinue then "Continue" + wordname.s + "/br"
else if kind = krecord then fsig2("Record" sub 1, nametype.s, paratypes.s)
else if kind = ksequence then "seq(:(worddata.s)):(resulttype.s)"
else if kind = kbr then
 "Br2("
 + toword.brt.s
 + ","
 + toword.brf.s
 + ")/br
 "
else if kind = kstart then
 "Start(:(resulttype.s))/br
 "
else if kind = kendblock then
 "EndBlock /br
 "
else if kind = kexit then
 "Exit /br
 "
else if kind = kloop then "Loop:(fsig2(wordname.s, nametype.s, paratypes.s) << 1):(para.module.s)/br"
else if kind = kfref then "FREF:(basesym.s)"
else
 (if name.module.s ∈ "internal" then "" else %.module.s + ":")
 + fsig2(wordname.s, nametype.s, paratypes.s)
 + %.resulttype.s

Function Lit(i:int) symbol
{OPTION INLINE}
symbol([toword.i], othermod, [typeint], tobits.i, tobits.kint)

Function Jmp(s:seq.symbol) seq.symbol
let returntype = resulttype.s sub 1
for islabel = false, good = true, e ∈ s >> 1
while good
do
 let kind = kind.e,
 next(
  not.islabel
  , islabel ∧ kind = klabel
  ∨ returntype = typeint ∧ kind = kint
  ∨ returntype = typeword ∧ kind = kword
 )
assert good report
 for txt = "Jmp format", e ∈ s do txt + %.e,
 txt,
[Jmp(n.s + 2, "JmpB", kjmpB)] + s + Jmp(n.s + 2, "Jmp", kjmp)

Function Label(value:int) symbol Jmp(value, ":", klabel)

function Jmp(i:int, name:seq.word, kind:symbolKind) symbol
{OPTION INLINE}
symbol(name, othermod, [typeint, type?], tobits.i, tobits.kind)

Function Lit(n:word) symbol
{OPTION INLINE}
symbol([n], othermod, [typeint], tobits.toint.n, tobits.kint)

Function Sequence(eletype:mytype, length:int) symbol
{Reduce to base type}
symbol(
 [toword.length]
 , moduleref("internallib $sequence", eletype)
 , [seqof.eletype]
 , tobits.length
 , tobits.ksequence
)

Function symbolC(i:int, libname:word) symbol
symbol(
 [merge.[libname, "." sub 1, toword.i]]
 , othermod
 , [typeptr]
 , 0x0
 , tobits.kconstantrecord
)

Function symbol4(
module:modref
, name:word
, namePara:mytype
, paras:seq.mytype
, rt:mytype
) symbol
let types = [namePara] + paras + rt
let kind =
 tobits(
  if name.module ∈ "$global" then kglobal
  else if name ∈ "abort" then{name.module = internal}symKind(module, name, [namePara] + paras, kcompoundname)
  else if name.module ∈ "builtin" then kbuiltincompound
  else kcompoundname
 ),
symbol([name], module, types, 0x0, kind)

Function ifthenelse(
cond:seq.symbol
, thenclause:seq.symbol
, elseclause:seq.symbol
, m:mytype
) seq.symbol
[Start.m] + cond + Br2(1, 2) + thenclause + Exit + elseclause + Exit + EndBlock

Function Littrue symbol symbol("true", internalmod, [typeboolean], 0x0, tobits.ktrue)

Function Litfalse symbol symbol("false", internalmod, [typeboolean], 0x0, tobits.kfalse)

Function Word(s:word) symbol
symbol([s], moduleref."internallib $word", [typeword], 0x0, tobits.kword)

Function Words(s:seq.word) symbol
symbol(s, moduleref."internallib $words", [typeptr], 0x0, tobits.kwords)

Function continue(i:int) symbol
symbol([toword.i], othermod, [type?], 0x0, tobits.kcontinue)

Function Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype) symbol
let xtypes =
 [typeref.[toword.firstvar, "." sub 1, "internallib" sub 1]] + types + resulttype,
symbol("LOOPBLOCK", moduleref("internallib internal", resulttype), xtypes, 0x0, tobits.kloop)

Function firstvar(a:symbol) int toint.abstracttypename.(types.a) sub 1

Function wordname(s:symbol) word (worddata.s) sub 1

Function typebits mytype typeref."bits bits *"

Function typebyte mytype typeref."byte bits *"

Function typeword mytype typeref."word kernal *"

Function deepcopyseqword symbol
symbol4(
 moduleref("* seq", typeword)
 , "type" sub 1
 , seqof.typeword
 , [seqof.typeword]
 , seqof.typeword
)

Function outofboundssymbol symbol
symbol(moduleref."* tausupport", "outofbounds", empty:seq.mytype, seqof.typeword)

Function encodenosym symbol
symbol(moduleref."* tausupport", "encodingno", [seqof.typeword], typeint)

Function Local(i:int) symbol Local(toword.i, typeint, i)

Function Define(i:int) symbol Define(toword.i, i)

Function Define(name:word, i:int) symbol
symbol([name], othermod, [typeint], tobits.i, tobits.kdefine)

Function Fref(s:symbol) symbol
let kind = kind.s
assert not.isconst.kind ∧ kind ≠ kglobal ∧ (worddata.s) sub 1 ∉ "FREF" report "FREF problem:(s)"
let a = flags.s << flagshift ∨ tobits.kfref,
symbol(worddata.s, module.s, types.s, raw.s, a)

function flagshift int 11

Function basesym(s:symbol) symbol
if kind.s = kfref then symbol(worddata.s, module.s, types.s, raw.s, flags.s >> flagshift)
else s

Function nametype(sym:symbol) seq.mytype
if issimplename.sym then empty:seq.mytype else [(types.sym) sub 1]

Function Local(name:word, type:mytype, parano:int) symbol
symbol([name], othermod, [type], tobits.parano, tobits.klocal)

function othermod modref moduleref."internallib $other"

Function builtinmod(para:mytype) modref moduleref("internallib builtin", para)

Function isencoding(t:mytype) boolean
(typerep.t) sub 1 = (typerep.typeref."encoding encoding *") sub 1

Function isseq(t:mytype) boolean (typerep.t) sub 1 = (typerep.typeref."seq seq *") sub 1

Function iscore4(typ:mytype) boolean
typ = typeint ∨ typ = typereal ∨ typ = typeptr ∨ typ = typeboolean

function genEnum seq.seq.word
["newType: symbolKind decodeName: % names: ? kfref kwords kword kint kreal kfalse ktrue kconstantrecord klocal kdefine ksequence krecord kloop kstart kbr kjmpB klabel kjmp kcontinue kexit kendblock kother kidxNB kidx kcompoundname kmember kcat kstacktrace knot kgetseqlength kgetseqtype keqlI keqlB keqlreal kintpart kcasttoreal ktoreal ktointbyte ktointbit krepresentation kmulreal kdivreal kaddreal ksubreal k>1real kmulint kdivint kaddint ksubint k>1int kgrtI k<<bits k>>bits kxorbits k∨bits k∧bits kabortR kabortI kabortB kabortP ksetI ksetR ksetP kprefref kbuiltin kglobal kmakereal kfld kcreatethreadZ kbuiltincompound kinternalmod"]

<<<< Below is auto generated code >>>>

type symbolKind is toint:int

Export toint(symbolKind) int

Export symbolKind(i:int) symbolKind

Export type:symbolKind

Function =(a:symbolKind, b:symbolKind) boolean toint.a = toint.b

Function kfref symbolKind symbolKind.1

Function kwords symbolKind symbolKind.2

Function kword symbolKind symbolKind.3

Function kint symbolKind symbolKind.4

Function kreal symbolKind symbolKind.5

Function kfalse symbolKind symbolKind.6

Function ktrue symbolKind symbolKind.7

Function kconstantrecord symbolKind symbolKind.8

Function klocal symbolKind symbolKind.9

Function kdefine symbolKind symbolKind.10

Function ksequence symbolKind symbolKind.11

Function krecord symbolKind symbolKind.12

Function kloop symbolKind symbolKind.13

Function kstart symbolKind symbolKind.14

Function kbr symbolKind symbolKind.15

Function kjmpB symbolKind symbolKind.16

Function klabel symbolKind symbolKind.17

Function kjmp symbolKind symbolKind.18

Function kcontinue symbolKind symbolKind.19

Function kexit symbolKind symbolKind.20

Function kendblock symbolKind symbolKind.21

Function kother symbolKind symbolKind.22

Function kidxNB symbolKind symbolKind.23

Function kidx symbolKind symbolKind.24

Function kcompoundname symbolKind symbolKind.25

Function kmember symbolKind symbolKind.26

Function kcat symbolKind symbolKind.27

Function kstacktrace symbolKind symbolKind.28

Function knot symbolKind symbolKind.29

Function kgetseqlength symbolKind symbolKind.30

Function kgetseqtype symbolKind symbolKind.31

Function keqlI symbolKind symbolKind.32

Function keqlB symbolKind symbolKind.33

Function keqlreal symbolKind symbolKind.34

Function kintpart symbolKind symbolKind.35

Function kcasttoreal symbolKind symbolKind.36

Function ktoreal symbolKind symbolKind.37

Function ktointbyte symbolKind symbolKind.38

Function ktointbit symbolKind symbolKind.39

Function krepresentation symbolKind symbolKind.40

Function kmulreal symbolKind symbolKind.41

Function kdivreal symbolKind symbolKind.42

Function kaddreal symbolKind symbolKind.43

Function ksubreal symbolKind symbolKind.44

Function k>1real symbolKind symbolKind.45

Function kmulint symbolKind symbolKind.46

Function kdivint symbolKind symbolKind.47

Function kaddint symbolKind symbolKind.48

Function ksubint symbolKind symbolKind.49

Function k>1int symbolKind symbolKind.50

Function kgrtI symbolKind symbolKind.51

Function k<<bits symbolKind symbolKind.52

Function k>>bits symbolKind symbolKind.53

Function kxorbits symbolKind symbolKind.54

Function k∨bits symbolKind symbolKind.55

Function k∧bits symbolKind symbolKind.56

Function kabortR symbolKind symbolKind.57

Function kabortI symbolKind symbolKind.58

Function kabortB symbolKind symbolKind.59

Function kabortP symbolKind symbolKind.60

Function ksetI symbolKind symbolKind.61

Function ksetR symbolKind symbolKind.62

Function ksetP symbolKind symbolKind.63

Function kprefref symbolKind symbolKind.64

Function kbuiltin symbolKind symbolKind.65

Function kglobal symbolKind symbolKind.66

Function kmakereal symbolKind symbolKind.67

Function kfld symbolKind symbolKind.68

Function kcreatethreadZ symbolKind symbolKind.69

Function kbuiltincompound symbolKind symbolKind.70

Function kinternalmod symbolKind symbolKind.71

Function %(code:symbolKind) seq.word
let discard =
 [
  kfref
  , kwords
  , kword
  , kint
  , kreal
  , kfalse
  , ktrue
  , kconstantrecord
  , klocal
  , kdefine
  , ksequence
  , krecord
  , kloop
  , kstart
  , kbr
  , kjmpB
  , klabel
  , kjmp
  , kcontinue
  , kexit
  , kendblock
  , kother
  , kidxNB
  , kidx
  , kcompoundname
  , kmember
  , kcat
  , kstacktrace
  , knot
  , kgetseqlength
  , kgetseqtype
  , keqlI
  , keqlB
  , keqlreal
  , kintpart
  , kcasttoreal
  , ktoreal
  , ktointbyte
  , ktointbit
  , krepresentation
  , kmulreal
  , kdivreal
  , kaddreal
  , ksubreal
  , k>1real
  , kmulint
  , kdivint
  , kaddint
  , ksubint
  , k>1int
  , kgrtI
  , k<<bits
  , k>>bits
  , kxorbits
  , k∨bits
  , k∧bits
  , kabortR
  , kabortI
  , kabortB
  , kabortP
  , ksetI
  , ksetR
  , ksetP
  , kprefref
  , kbuiltin
  , kglobal
  , kmakereal
  , kfld
  , kcreatethreadZ
  , kbuiltincompound
  , kinternalmod
 ]
let i = toint.code,
if between(i, 1, 71) then
 let r =
  [
   "kfref kwords kword kint kreal kfalse ktrue kconstantrecord klocal kdefine ksequence krecord kloop kstart kbr kjmpB klabel kjmp kcontinue kexit kendblock kother kidxNB kidx kcompoundname kmember kcat kstacktrace knot kgetseqlength kgetseqtype keqlI keqlB keqlreal kintpart kcasttoreal ktoreal ktointbyte ktointbit krepresentation kmulreal kdivreal kaddreal ksubreal k>1real kmulint kdivint kaddint ksubint k>1int kgrtI k<<bits k>>bits kxorbits k∨bits k∧bits kabortR kabortI kabortB kabortP ksetI ksetR ksetP kprefref kbuiltin kglobal kmakereal kfld kcreatethreadZ kbuiltincompound kinternalmod"
   sub i
  ],
 if r ≠ "?" then r else "symbolKind." + toword.i
else "symbolKind." + toword.i 