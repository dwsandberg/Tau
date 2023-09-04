Module symbol

use bits

use mytype

use otherseq.mytype

use standard

use set.symbol

use set.symdef

use seq.typedef

use otherseq.word

Export >2(symbol, symbol) ordering

Export type:symbol

Export module(symbol) modref

Export types(symbol) seq.mytype

Export worddata(symbol) seq.word

Export type:symdef

Export paragraphno(symdef) int

Export sym(sd:symdef) symbol

Export symdef(sym:symbol, code:seq.symbol, p:int) symdef

Export typebase(i:int) mytype {From mytype}

Export type:modref {From mytype}

Export %(modref) seq.word {From mytype}

Export isAbstract(modref) boolean {From mytype}

Export isSimple(modref) boolean {From mytype}

Export library(modref) word {From mytype}

Export name(modref) word {From mytype}

Export para(modref) mytype {From mytype}

Export type:mytype {From mytype}

Export %(p:mytype) seq.word {From mytype}

Export abstractModref(mytype) modref {From mytype}

Export abstracttype(mytype) mytype {From mytype}

Export abstracttypename(mytype) word {From mytype}

Export isAbstract(m:mytype) boolean {From mytype}

Export parameter(mytype) mytype {From mytype}

Export processof(mytype) mytype {From mytype}

Export seqof(mytype) mytype {From mytype}

Export tomodref(mytype) modref {From mytype}

Export type:passtypes {From mytype}

Export moduleref(seq.word) modref {From mytype}

Export typeref(seq.word) mytype {From mytype}

Export =(a:modref, b:modref) boolean {From mytype}

Export =(t:mytype, b:mytype) boolean {From mytype}

Export >1(modref, modref) ordering {From mytype}

Export >1(typedef, typedef) ordering {From mytype}

Export addabstract(a:mytype, t:mytype) mytype {From mytype}

Export internalmod modref {From mytype}

Export moduleref(seq.word, para:mytype) modref {From mytype}

Export replaceT(mytype, modref) modref {From mytype}

Export replaceT(with:mytype, m:mytype) mytype {From mytype}

Export typeT mytype {From mytype}

Export typeboolean mytype {From mytype}

Export typeint mytype {From mytype}

Export typeptr mytype {From mytype}

Export typereal mytype {From mytype}

Export type:set.symbol {From set.symbol}

type symbol is worddata:seq.word, module:modref, types:seq.mytype, raw:bits, flags:bits

function maplibrary(libname:word, map:seq.word) word
let match = 1
let nomatch = 2
let done = 3
for state = 0, result = libname, x ∈ map
while state ≠ done
do
 if state = nomatch then
 next(0, result)
 else if state = match then
 next(done, x)
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
 ∧ ((flags.a ⊻ flags.b) ∧ (simplenamebit ∨ frefbit ∨ unboundbit)) = 0x0

Function same(a:symbol, b:symbol) boolean
types.a = types.b
 ∧ worddata.a = worddata.b
 ∧ flags.a = flags.b
 ∧ raw.a = raw.b
 ∧ name.module.a = name.module.b
 ∧ para.module.a = para.module.b
 ∧ library.module.a = library.module.b

Function >1(a:symbol, b:symbol) ordering
a >2 b
 ∧ module.a >1 module.b
 ∧ toint((flags.a ⊻ flags.b) ∧ (frefbit ∨ unboundbit)) >1 0

Function >2(a:symbol, b:symbol) ordering
worddata.a >1 worddata.b
 ∧ types.a >> 1 >1 types.b >> 1
 ∧ issimplename.a >1 issimplename.b

Function privatefields(s:symbol) seq.int [toint.raw.s, toint.flags.s]

Function Words(s:seq.word) symbol
symbol(s, moduleref."internallib $words", [typeptr], 0x0, constbit)

Function constbit bits bits.1

function simplenamebit bits bits.2

function specialbit bits bits.4

function frefbit bits bits.8

Function hasfrefbit bits bits.16

function unboundbit bits 0x20

function requiresbit bits 0x40

Function hasfref(sym:symbol) boolean (flags.sym ∧ (hasfrefbit ∨ frefbit)) ≠ 0x0

Function issimplename(sym:symbol) boolean (flags.sym ∧ simplenamebit) ≠ 0x0

Function isspecial(s:symbol) boolean (flags.s ∧ specialbit) ≠ 0x0

Function isFref(s:symbol) boolean (flags.s ∧ frefbit) ≠ 0x0

Function isconst(s:symbol) boolean (flags.s ∧ constbit) ≠ 0x0

Function isunbound(sym:symbol) boolean (flags.sym ∧ unboundbit) ≠ 0x0

Function hasrequires(sym:symbol) boolean (flags.sym ∧ requiresbit) ≠ 0x0

Function hash(sym:symbol) int hash(types.sym, worddata.sym)

Function setunbound(sym:symbol) symbol
symbol(worddata.sym, module.sym, types.sym, raw.sym, flags.sym ∨ unboundbit)

Function setrequires(sym:symbol) symbol
symbol(worddata.sym, module.sym, types.sym, raw.sym, flags.sym ∨ requiresbit)

Function replaceTsymbol(with:mytype, sym:symbol) symbol
if with = typeT ∨ isconst.sym then
sym
else
 for newtypes = empty:seq.mytype, t ∈ types.sym do newtypes + replaceT(with, t)
 let newmodule = replaceT(with, module.sym)
 let newhash =
  if true ∨ not.isunbound.sym ∨ isAbstract.newmodule then
  flags.sym
  else (unboundbit ⊻ bits.-1) ∧ flags.sym,
 symbol(worddata.sym, newmodule, newtypes, raw.sym, newhash)

function symbolZ(
 module:modref
 , name:word
 , namePara:seq.mytype
 , paras:seq.mytype
 , rt:mytype
 , flags:bits
 , raw:bits
) symbol
let types = namePara + paras + rt,
symbol([name], module, types, raw, if isempty.namePara then simplenamebit ∨ flags else flags)

Function Br2(t:int, f:int) symbol
let raw = bits.t << 20 ∨ bits.f,
symbolZ(
 moduleref."internallib $br"
 , 1_"BR2"
 , [typeref.[toword.toint.raw, 1_".", 1_"internallib"]]
 , empty:seq.mytype
 , type?
 , specialbit
 , bits.t << 20 ∨ bits.f
)

Function TBr(t:int, f:int) symbol
let raw = bits.t << 20 ∨ bits.f,
symbolZ(
 moduleref."internallib $tbr"
 , 1_"TBR"
 , [typeref.[toword.toint.raw, 1_".", 1_"internallib"]]
 , empty:seq.mytype
 , type?
 , specialbit
 , bits.t << 20 ∨ bits.f
)

Function brt(s:symbol) int toint(raw.s >> 20 ∧ 0xFFFFF)

Function brf(s:symbol) int toint(raw.s ∧ 0xFFFFF)

Function type? mytype typeref."? internal internallib"

Function name(sym:symbol) word 1_worddata.sym

Function iswords(s:symbol) boolean name.module.s ∈ "$words"

Function islocal(s:symbol) boolean name.module.s ∈ "$local"

Function isdefine(s:symbol) boolean name.module.s ∈ "$define"

Function isbr(s:symbol) boolean name.module.s ∈ "$br"

Function isExit(s:symbol) boolean name.module.s ∈ "$exitblock"

Function value(sym:symbol) int toint.raw.sym

Function nopara(s:symbol) int
if isconst.s ∨ islocal.s ∨ isFref.s then
0
else if isspecial.s ∧ name.module.s ∉ "$record $loopblock" then
 if isdefine.s ∨ isbr.s ∨ isExit.s then
 1
 else assert name.module.s ∈ "$continue $sequence" report "CHeKC^(s)", toint.name.s
else n.types.s - if issimplename.s then 1 else 2

function fsig2(name:word, nametype:seq.mytype, paratypes:seq.mytype) seq.word
let fullname = if isempty.nametype then [name] else [name] + ":" + %.1_nametype,
if n.paratypes = 0 then
fullname
else for acc = fullname + "(", t ∈ paratypes do acc + %.t + ",", acc >> 1 + ")"

Function istype(s:symbol) boolean
not.issimplename.s ∧ wordname.s = 1_"type" ∧ nopara.s = 1

Function Record(types:seq.mytype) symbol
symbol(moduleref."internallib $record", "RECORD", types, typeptr, specialbit)

Function Reallit(i:int) symbol
symbolZ(
 moduleref."internallib $real"
 , toword.i
 , empty:seq.mytype
 , empty:seq.mytype
 , typereal
 , constbit
 , tobits.i
)

Function Exit symbol symbol(moduleref."internallib $exitblock", "EXITBLOCK", type?, specialbit)

Function Start(t:mytype) symbol
symbol(moduleref("internallib $loopblock", t), "Start", t, specialbit)

Function EndBlock symbol symbol(moduleref."internallib $block", "BLOCK", typeint, specialbit)

Function NotOp symbol symbol(internalmod, "not", typeboolean, typeboolean)

Function PlusOp symbol symbol(internalmod, "+", typeint, typeint, typeint)

Function JumpOp symbol symbol(internalmod, "Jump", typeint, typeint, typeboolean)

Function paratypes(s:symbol) seq.mytype
if isFref.s then
empty:seq.mytype
else if issimplename.s then
types.s >> 1
else subseq(types.s, 2, n.types.s - 1)

Function resulttype(s:symbol) mytype if isFref.s then typeint else 1^types.s

Function fullname(s:symbol) seq.word
if issimplename.s then [name.s] else [name.s] + ":" + %.1_types.s

Function %(s:symbol) seq.word
if islocal.s then
"^(merge([1_"%"] + wordname.s))"
else if name.module.s ∈ "$int $real" then
[name.s]
else if iswords.s then
if 1_dq ∈ worddata.s then "'^(worddata.s) '" else dq.worddata.s
else if isword.s then
"WORD" + wordname.s
else if isrecordconstant.s then
[name.s]
else if isFref.s then
"FREF^(basesym.s)"
else if isloopblock.s then
"Loop^(fsig2(wordname.s, nametype.s, paratypes.s) << 1)^(para.module.s) /br"
else if not.isspecial.s then
 (if name.module.s ∈ "internal" then "" else %.module.s + ":")
 + fsig2(wordname.s, nametype.s, paratypes.s)
 + %.resulttype.s
else if isdefine.s then
"Define^(name.s)"
else if isstart.s then
"Start (^(resulttype.s)) /br"
else if isblock.s then
"EndBlock /br"
else if isExit.s then
"Exit /br"
else if isbr.s then
"Br2 (" + toword.brt.s + "," + toword.brf.s + ") /br"
else if iscontinue.s then
"Continue" + wordname.s + "/br"
else if isRecord.s then
fsig2(1_"Record", nametype.s, paratypes.s)
else if isSequence.s then
"seq (^(worddata.s))^(resulttype.s)"
else %.module.s + ":" + fsig2(wordname.s, nametype.s, paratypes.s) + %.resulttype.s

Function Lit(i:int) symbol
{OPTION INLINE}
symbolZ(
 moduleref."internallib $int"
 , toword.i
 , empty:seq.mytype
 , empty:seq.mytype
 , typeint
 , constbit
 , tobits.i
)

Function Sequence(eletype:mytype, length:int) symbol
symbolZ(
 moduleref("internallib $sequence", eletype)
 , toword.length
 , empty:seq.mytype
 , empty:seq.mytype
 , seqof.eletype
 , specialbit ∨ simplenamebit
 , tobits.length
)

Function symbol(m:modref, name:seq.word, returntype:mytype, b:bits) symbol
symbol(m, name, empty:seq.mytype, returntype, b)

Function symbol(module:modref, name:seq.word, paras:seq.mytype, rt:mytype) symbol
symbol(module, name, paras, rt, 0x0)

Function symbol(
 module:modref
 , name:seq.word
 , para:mytype
 , para2:mytype
 , para3:mytype
 , returntype:mytype
) symbol
symbol(module, name, [para, para2, para3], returntype)

Function symbol(
 module:modref
 , name:seq.word
 , para:mytype
 , para2:mytype
 , returntype:mytype
) symbol
symbol(module, name, [para, para2], returntype)

Function symbol(module:modref, name:seq.word, para:mytype, returntype:mytype) symbol
symbol(module, name, [para], returntype)

Function symbol(module:modref, name:seq.word, returntype:mytype) symbol
symbol(module, name, empty:seq.mytype, returntype)

Function symbol(
 module:modref
 , name:seq.word
 , paras:seq.mytype
 , rt:mytype
 , flags:bits
) symbol
symbolZ(module, 1_name, empty:seq.mytype, paras, rt, flags, 0x0)

Function symbol4(
 module:modref
 , name:word
 , namePara:mytype
 , paras:seq.mytype
 , rt:mytype
) symbol
symbolZ(module, name, [namePara], paras, rt, if name ∈ "LOOPBLOCK" then specialbit else 0x0, 0x0)

Function ifthenelse(
 cond:seq.symbol
 , thenclause:seq.symbol
 , elseclause:seq.symbol
 , m:mytype
) seq.symbol
[Start.m] + cond + Br2(1, 2) + thenclause + Exit + elseclause + Exit + EndBlock

Function Littrue symbol symbol(internalmod, "true", typeboolean, constbit)

Function Litfalse symbol symbol(internalmod, "false", typeboolean, constbit)

Function continue(i:int) symbol
symbol(moduleref."internallib $continue", [toword.i], type?, specialbit)

Function Word(s:word) symbol symbol(moduleref."internallib $word", [s], typeword, constbit)

Function isstartorloop(sym:symbol) boolean name.module.sym ∈ "$loopblock"

Function isstart(sym:symbol) boolean
name.module.sym = 1_"$loopblock" ∧ wordname.sym ≠ 1_"LOOPBLOCK"

Function isloopblock(s:symbol) boolean
name.module.s = 1_"$loopblock" ∧ wordname.s = 1_"LOOPBLOCK"

Function Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype) symbol
symbol4(
 moduleref("internallib $loopblock", resulttype)
 , 1_"LOOPBLOCK"
 , typeref.[toword.firstvar, 1_".", 1_"internallib"]
 , types
 , resulttype
)

Function firstvar(a:symbol) int toint.abstracttypename.1_types.a

Function EqOp symbol symbol(internalmod, "=", typeint, typeint, typeboolean)

Function GtOp symbol symbol(internalmod, ">", typeint, typeint, typeboolean)

Function isblock(s:symbol) boolean name.module.s = 1_"$block"

Function iscontinue(s:symbol) boolean name.module.s ∈ "$continue"

Function isSequence(s:symbol) boolean name.module.s = 1_"$sequence"

Function isRecord(s:symbol) boolean name.module.s = 1_"$record"

Function iswordseq(s:symbol) boolean name.module.s = 1_"$words"

Function isword(s:symbol) boolean name.module.s ∈ "$word"

Function isIntLit(s:symbol) boolean name.module.s ∈ "$int"

Function isRealLit(s:symbol) boolean name.module.s ∈ "$real"

Function isrecordconstant(s:symbol) boolean name.module.s = 1_"$constant"

Function wordname(s:symbol) word 1_worddata.s

Function typebits mytype typeref."bits bits *"

Function typebyte mytype typeref."byte bits *"

Function typeword mytype typeref."word words *"

Function typechar mytype typeref."char standard *"

Function isseq(t:mytype) boolean 1_typerep.t = 1_typerep.typeref."seq seq *"

Function packedtypes seq.mytype
[
 typeref."packed2 tausupport *"
 , typeref."packed3 tausupport *"
 , typeref."packed4 tausupport *"
 , typeref."packed5 tausupport *"
 , typeref."packed6 tausupport *"
]

Function deepcopyseqword symbol
symbol4(moduleref("* seq", typeword), 1_"type", seqof.typeword, [seqof.typeword], seqof.typeword)

Function makerealSymbol symbol symbol(moduleref."* real", "makereal", seqof.typeword, typereal)

Function indexsymbol(T:mytype) symbol
symbol(moduleref("* seq", T), "_", typeint, seqof.T, T)

Function outofboundssymbol symbol
symbol(moduleref."* tausupport", "outofbounds", seqof.typeword)

Function encodenosym symbol
symbol(moduleref."* tausupport", "encodingno", seqof.typeword, typeint)

Function blockitsymbol(T:mytype) symbol symbol(moduleref."* tausupport", "blockIt", T, T)

Function isconstantorspecial(s:symbol) boolean isconst.s ∨ isspecial.s

Function Local(i:int) symbol Local(toword.i, typeint, i)

Function Define(i:int) symbol Define(toword.i, i)

Function Define(name:word, i:int) symbol
symbolZ(
 moduleref."internallib $define"
 , name
 , empty:seq.mytype
 , empty:seq.mytype
 , typeint
 , specialbit
 , tobits.i
)

Function Fref(s:symbol) symbol
assert not.isconst.s ∧ 1_worddata.s ∉ "FREF" ∧ not.isGlobal.s
report "FREF problem^(s)^(stacktrace)"
let z = constbit ∨ frefbit ∨ flags.s,
symbol(worddata.s, module.s, types.s, raw.s, z)

Function basesym(s:symbol) symbol
if isFref.s then
 let flags = flags.s ∧ (constbit ∨ frefbit ∨ hasfrefbit ⊻ tobits.-1),
 symbol(worddata.s, module.s, types.s, raw.s, flags)
else s

Function GetSeqLength symbol symbol(internalmod, "getseqlength", typeptr, typeint)

Function GetSeqType symbol symbol(internalmod, "getseqtype", typeptr, typeint)

Function nametype(sym:symbol) seq.mytype
if issimplename.sym then empty:seq.mytype else [1_types.sym]

Function PreFref symbol
{symbol (internalmod," PreFref", typeptr)}
symbol(internalmod, "PreFref", empty:seq.mytype, typeptr, specialbit)

Function Local(name:word, type:mytype, parano:int) symbol
symbolZ(
 moduleref."internallib $local"
 , name
 , empty:seq.mytype
 , empty:seq.mytype
 , type
 , specialbit
 , tobits.parano
)

Function inModFor(sym:symbol) boolean name.module.sym = 1_"$FOR"

Function builtinmod(para:mytype) modref moduleref("internallib builtin", para)

Function isBuiltin(sym:symbol) boolean name.module.sym = 1_"builtin"

Function isInternal(sym:symbol) boolean name.module.sym = 1_"internal"

Function isGlobal(sym:symbol) boolean name.module.sym = 1_"$global"

Function isencoding(t:mytype) boolean
1_typerep.t = 1_typerep.typeref."encoding encoding *"

Function deepcopySym(rt:mytype) symbol
if rt = typereal then
symbol(moduleref."* tausupport", "deepcopy", typereal, typereal)
else if rt = typeint then
symbol(moduleref."* tausupport", "deepcopy", typeint, typeint)
else symbol4(replaceT(parameter.rt, abstractModref.rt), 1_"type", rt, [rt], rt)

Function iscore4(typ:mytype) boolean
typ = typeint ∨ typ = typereal ∨ typ = typeptr ∨ typ = typeboolean

Function setSym(typ:mytype) symbol
let fldtype = if isseq.typ then typeptr else if isencoding.typ then typeint else typ,
symbol(if iscore4.fldtype then internalmod else builtinmod.fldtype, "set", typeptr, fldtype, typeptr)

Function Getfld(fldtype:mytype) symbol
let kind2 =
 if isseq.fldtype then
 typeptr
 else if isencoding.fldtype ∨ fldtype = typeword then
 typeint
 else fldtype,
symbol(builtinmod.kind2, "fld", typeptr, typeint, kind2)

type symdef is sym:symbol, code:seq.symbol, bits:bits

function symdef(sym:symbol, code:seq.symbol, pno:int) symdef symdef(sym, code, bits.pno)

Function paragraphno(sd:symdef) int toint(0xFFFFFFFFFFFF ∧ bits.sd)

Function externalNo(sd:symdef) int toint(0xFFFFFFFFFFFF ∧ bits.sd)

Function >1(a:symdef, b:symdef) ordering sym.a >1 sym.b

Function getSymdef(a:set.symdef, sym:symbol) set.symdef
lookup(a, symdef(sym, empty:seq.symbol, 0))

function ThisLibrary bits 0x1000000000000

function PROFILE bits 0x2000000000000

Function STATE bits 0x4000000000000

Function COMPILETIME bits 0x8000000000000

Function NOINLINE bits 0x10000000000000

function INLINE bits 0x20000000000000

Function VERYSIMPLE bits 0x40000000000000

Function ENTRYPOINT bits 0x80000000000000

Function isThisLibrary(sd:symdef) boolean (bits.sd ∧ ThisLibrary) ≠ 0x0

Function isPROFILE(sd:symdef) boolean (bits.sd ∧ PROFILE) ≠ 0x0

Function isCOMPILETIME(sd:symdef) boolean (bits.sd ∧ COMPILETIME) ≠ 0x0

Function isINLINE(sd:symdef) boolean (bits.sd ∧ INLINE) ≠ 0x0

Function isNOINLINE(sd:symdef) boolean (bits.sd ∧ NOINLINE) ≠ 0x0

Function isVERYSIMPLE(sd:symdef) boolean (bits.sd ∧ VERYSIMPLE) ≠ 0x0

Function hasState(sd:symdef) boolean (bits.sd ∧ STATE) ≠ 0x0

function A1(opts:seq.word) bits
for acc = 0x0, w ∈ opts
do
 let i = findindex("ThisLibrary PROFILE STATE COMPILETIME NOINLINE INLINE VERYSIMPLE ENTRYPOINT", w),
 acc ∨ 0x1 << (47 + i),
acc

Function symdef4(sym:symbol, code:seq.symbol, paragraphno:int, options:seq.word) symdef
symdef(sym, code, bits.paragraphno ∨ A1.options)

Function symdef4(sym:symbol, code:seq.symbol, paragraphno:int, options:bits) symdef
symdef(sym, code, bits.paragraphno ∨ options ∧ 0xFFFF000000000000)

Function getOptions(sd:symdef) seq.word
for
 result = ""
 , acc = bits.sd >> 48
 , w ∈ "ThisLibrary PROFILE STATE COMPILETIME NOINLINE INLINE VERYSIMPLE ENTRYPOINT"
do if (acc ∧ 0x1) = 0x1 then next(result + w, acc >> 1) else next(result, acc >> 1),
result

Function getOptionsBits(sd:symdef) bits bits.sd

Export code(symdef) seq.symbol

Function getCode(a:set.symdef, sym:symbol) seq.symbol
let b = getSymdef(a, sym),
if isempty.b then empty:seq.symbol else code.1_b 