Module symbol

use bits

use mytype

use standard

use words

use seq.char

use otherseq.mytype

use seq.mytype

use encoding.symbol

use seq.symbol

use set.symbol

use set.symdef

use seq.typedef

use otherseq.word

use set.word

use seq.seq.char

use otherseq.seq.word

use seq.seq.word

Export type:passtypes

Export abstractModref(mytype)modref

Export print(modref)seq.word

Export replaceT(mytype, modref)modref

Export type:symbol

Export typeint mytype

Export typeptr mytype

Export typeboolean mytype

Export typereal mytype

Export type:set.symbol

Export type:mytype

Export isabstract(m:mytype)boolean

Export parameter(mytype)mytype

Export print(p:mytype)seq.word

Export=(t:mytype, b:mytype)boolean

Export replaceT(with:mytype, m:mytype)mytype

Export iscomplex(a:mytype)boolean

Export worddata(s:symbol)seq.word

Export=(a:modref, b:modref)boolean

---internal

type symbol is worddata:seq.word, module:modref, types:seq.mytype, raw:bits, hashbits:bits

Export type:symbol

Export worddata(symbol)seq.word

Export module(symbol)modref

Export types(symbol)seq.mytype

Export raw(symbol)bits

Function rehash(s:symbol)symbol
symbol(worddata.s, module.s, types.s, raw.s, 
extrabits(types.s >> 1, worddata.s, hashbits.s))

Function =(a:symbol, b:symbol)boolean
  worddata.a = worddata.b ∧ types.a >> 1 = types.b >> 1
∧  module.a = module.b
∧  (xor(hashbits.a,hashbits.b) /and (simplenamebit /or frefbit))=0x0

Function ?(a:symbol, b:symbol)ordering
 ?2(a,b)
∧  module.a ? module.b

Function ?2(a:symbol, b:symbol)ordering
worddata.a ? worddata.b 
∧ types.a >> 1 ? types.b >> 1 
∧  toint(xor(hashbits.a,hashbits.b) /and   (simplenamebit /or frefbit)) ? 0


function hashshift int 5 

function hashmask bits 0x1F

function extrabits(types:seq.mytype, other:seq.word, flags:bits)bits bits.hash(types, other) << hashshift ∨ flags ∧ hashmask

Function extrabits(s:symbol)int toint.hashbits.s

Function Words(s:seq.word)symbol
symbol(s
, moduleref."internallib $words"
, [typeptr]
, 0x0
, extrabits(empty:seq.mytype, s, constbit)
)

function hasfrefbit bits bits.16

Function hasfref(sym:symbol)boolean(hashbits.sym ∧ (hasfrefbit ∨ frefbit)) ≠ 0x0

function frefbit bits bits.8

function specialbit bits bits.4

function simplenamebit bits bits.2

function constbit bits bits.1

function unboundbit bits 0x1 << 41

function requiresbit bits 0x1 << 42

Function issimplename(sym:symbol)boolean(hashbits.sym ∧ simplenamebit) ≠ 0x0

Function isspecial(s:symbol)boolean(hashbits.s ∧ specialbit) = specialbit

Function isFref(s:symbol)boolean(hashbits.s ∧ frefbit) = frefbit

Function isconst(s:symbol)boolean(hashbits.s ∧ constbit) = constbit

Function isunbound(sym:symbol)boolean(raw.sym ∧ unboundbit) ≠ 0x0



Function hasrequires(sym:symbol)boolean(raw.sym ∧ requiresbit) ≠ 0x0

Function hash(sym:symbol)int toint(hashbits.sym >> hashshift)

Function setunbound(sym:symbol)symbol symbol(worddata.sym, module.sym, types.sym, raw.sym ∨ unboundbit, hashbits.sym)

Function setrequires(sym:symbol)symbol symbol(worddata.sym, module.sym, types.sym, raw.sym ∨ requiresbit, hashbits.sym)

Function replaceTsymbol(with:mytype, sym:symbol)symbol
if with = typeT ∨ isconst.sym then sym
else
 let newtypes = 
  for newtypes = empty:seq.mytype, t ∈ types.sym do newtypes + replaceT(with, t)/for(newtypes)
 let adjustedraw = 
  {if isunbound.sym then for hasT=false, t=newtypes while not.hasT do isabstract.t /for(if hasT then raw.sym else raw.
sym /and xor(unboundbit, tobits.-1))else}
  raw.sym
 symbol(worddata.sym
 , replaceT(with, module.sym)
 , newtypes
 , adjustedraw
 , extrabits(newtypes, worddata.sym, hashbits.sym)
 )

function symbolZ(module:modref, name:word, namePara:seq.mytype, paras:seq.mytype, rt:mytype, flags:bits, raw:bits)symbol
let types = namePara + paras + rt
symbol([name]
, module
, types
, raw
, extrabits(types, [name], if isempty.namePara then simplenamebit ∨ flags else flags)
)

Function Br2(t:int, f:int)symbol
let raw = bits.t << 20 ∨ bits.f
symbolZ(moduleref."internallib $br"
, "BR2"_1
, [typeref.[toword.toint.raw, "."_1, "internallib"_1]]
, empty:seq.mytype
, type?
, specialbit
, bits.t << 20 ∨ bits.f
)

Function brt(s:symbol)int toint(raw.s >> 20 ∧ 0xFFFFF)

Function brf(s:symbol)int toint(raw.s ∧ 0xFFFFF)

Function type? mytype typeref."? internal internallib"

Function printrep(s:symbol)seq.word
if name.module.s = "$int"_1 then[name.s]
else if iswords.s then dq.worddata.s
else
 "(" + [library.module.s, name.module.s] + printrep.para.module.s + name.s
 + toword.toint.raw.s
 + for acc = "", t ∈ types.s do acc + printrep.t /for(acc + ")")

Function name(sym:symbol)word first.worddata.sym

Function iswords(s:symbol)boolean name.module.s ∈ "$words"

Function islocal(s:symbol)boolean name.module.s ∈ "$local"

Function isdefine(s:symbol)boolean name.module.s ∈ "$define"

Function isbr(s:symbol)boolean name.module.s ∈ "$br"

Function isexit(s:symbol)boolean name.module.s ∈ "$exitblock"

Function value(sym:symbol)int toint.raw.sym

Function nopara(s:symbol)int
if isconst.s ∨ islocal.s ∨ isFref.s then 0
else if isspecial.s ∧ name.module.s ∉ "$record $loopblock"then
 if isdefine.s ∨ isbr.s ∨ isexit.s then 1
 else{assert name.module.s /in"$continue $sequence"report"CHeKC"+print.s}toint.name.s
else length.types.s - if issimplename.s then 1 else 2

Export raw(symbol)bits

Export type:symbol

Export worddata(symbol)seq.word

Export module(symbol)modref

Export types(symbol)seq.mytype

Export=(a:symbol, b:symbol)boolean

Export ?(a:symbol, b:symbol)ordering

Export ?2(a:symbol, b:symbol)ordering

Export Words(s:seq.word)symbol

Export issimplename(sym:symbol)boolean

Export isspecial(s:symbol)boolean

Export isconst(s:symbol)boolean

Export isunbound(sym:symbol)boolean

Export hash(sym:symbol)int

Export setunbound(sym:symbol)symbol

Export setrequires(sym:symbol)symbol

Export replaceTsymbol(with:mytype, sym:symbol)symbol

Export Br2(l1:int, l2:int)symbol

Export brt(s:symbol)int

Export brf(s:symbol)int

Export name(sym:symbol)word

Export iswords(s:symbol)boolean

Export islocal(s:symbol)boolean

Export isdefine(s:symbol)boolean

Export isbr(symbol)boolean

Export isexit(s:symbol)boolean

Export value(sym:symbol)int

Export nopara(sym:symbol)int

---end internal


function fsig2(name:word, nametype:seq.mytype, paratypes:seq.mytype)seq.word
let fullname = 
 if isempty.nametype then[name]else[name] + ":" + print.first.nametype
if length.paratypes = 0 then fullname
else
 for acc = fullname + "(", t ∈ paratypes do acc + print.t + ", "/for(acc >> 1 + ")")

_______________________________

Function istype(s:symbol)boolean not.issimplename.s ∧ wordname.s = "type"_1 ∧ nopara.s = 1

Function Record(types:seq.mytype)symbol
symbol(moduleref."internallib $record", "RECORD", types, typeptr, specialbit)

Function Reallit(i:int)symbol
symbolZ(moduleref."internallib $real"
, toword.i
, empty:seq.mytype
, empty:seq.mytype
, typereal
, constbit
, tobits.i
)

----------------------

Function Exit symbol symbol(moduleref."internallib $exitblock", "EXITBLOCK", type?, specialbit)

Function Start(t:mytype)symbol
symbol(moduleref("internallib $loopblock", t), "Start", t, specialbit)

Function EndBlock symbol symbol(moduleref."internallib $block", "BLOCK", typeint, specialbit)

Function NotOp symbol symbol(internalmod, "not", typeboolean, typeboolean)

Function PlusOp symbol symbol(internalmod, "+", typeint, typeint, typeint)

Function paratypes(s:symbol)seq.mytype
if isFref.s then empty:seq.mytype
else if issimplename.s then types.s >> 1 else subseq(types.s, 2, length.types.s - 1)

Function resulttype(s:symbol)mytype if isFref.s then typeint else last.types.s

Function fullname(s:symbol)seq.word
if issimplename.s then[name.s]else[name.s] + ":" + print.first.types.s

Function print(s:symbol)seq.word
if islocal.s then
 {let x=toword.value.s[merge("%"+if x=name.s then[x]else[x, first.".", name.s]/if)]}
 [merge(["%"_1] + wordname.s)]
else if name.module.s ∈ "$int $real"then[name.s]
else if iswords.s then
 if dq_1 ∈ worddata.s then"'" + worddata.s + "'"else dq.worddata.s
else if isword.s then"WORD" + wordname.s
else if isrecordconstant.s then"const" + name.s
else if isFref.s then"FREF" + print.basesym.s
else if not.isspecial.s ∨ isloopblock.s then
 print.module.s + ":" + fsig2(wordname.s, nametype.s, paratypes.s)
 + if isloopblock.s then" /br"else print.resulttype.s
else if isdefine.s then"Define" + name.s
else if isstart.s then"Start" + "(" + print.resulttype.s + ") /br"
else if isblock.s then"EndBlock  /br"
else if isexit.s then"Exit  /br"
else if isbr.s then"Br2(" + toword.brt.s + ", " + toword.brf.s + ") /br"
else if iscontinue.s then"CONTINUE" + wordname.s + " /br"
else print.module.s + ":" + fsig2(wordname.s, nametype.s, paratypes.s) + print.resulttype.s

Function print(s:seq.symbol)seq.word for acc = "", sym ∈ s do acc + print.sym /for(acc)

Function Lit(i:int)symbol
{OPTION INLINE}
symbolZ(moduleref."internallib $int"
, toword.i
, empty:seq.mytype
, empty:seq.mytype
, typeint
, constbit
, tobits.i
)

Function Sequence(eletype:mytype, length:int)symbol
symbolZ(moduleref("internallib $sequence", eletype)
, toword.length
, empty:seq.mytype
, empty:seq.mytype
, seqof.eletype
, specialbit ∨ simplenamebit
, tobits.length
)

Function symbol(m:modref, name:seq.word, returntype:mytype, b:bits)symbol
symbol(m, name, empty:seq.mytype, returntype, b)

Function symbol(module:modref, name:seq.word, paras:seq.mytype, rt:mytype)symbol symbol(module, name, paras, rt, 0x0)

Function symbol(module:modref, name:seq.word, para:mytype, para2:mytype, para3:mytype, returntype:mytype)symbol
symbol(module, name, [para, para2, para3], returntype)

Function symbol(module:modref, name:seq.word, para:mytype, para2:mytype, returntype:mytype)symbol
symbol(module, name, [para, para2], returntype)

Function symbol(module:modref, name:seq.word, para:mytype, returntype:mytype)symbol
symbol(module, name, [para], returntype)

Function symbol(module:modref, name:seq.word, returntype:mytype)symbol
symbol(module, name, empty:seq.mytype, returntype)

Function symbol(module:modref, name:seq.word, paras:seq.mytype, rt:mytype, hashbits:bits)symbol
symbolZ(module, name_1, empty:seq.mytype, paras, rt, hashbits, 0x0)

Function symbol4(module:modref, name:word, namePara:mytype, paras:seq.mytype, rt:mytype)symbol
symbolZ(module
, name
, [namePara]
, paras
, rt
, if name ∈ "LOOPBLOCK"then specialbit else 0x0
, 0x0
)

Function ifthenelse(cond:seq.symbol, thenclause:seq.symbol, elseclause:seq.symbol, m:mytype)seq.symbol
[Start.m] + cond + Br2(1, 2) + thenclause + Exit + elseclause + Exit + EndBlock

Function Littrue symbol symbol(internalmod, "true", typeboolean, constbit)

Function Litfalse symbol symbol(internalmod, "false", typeboolean, constbit)

Function continue(i:int)symbol symbol(moduleref."internallib $continue", [toword.i], type?, specialbit)

Function Word(s:word)symbol symbol(moduleref."internallib $word", [s], typeword, constbit)

Function isstartorloop(sym:symbol)boolean name.module.sym ∈ "$loopblock"

Function isstart(sym:symbol)boolean name.module.sym = "$loopblock"_1 ∧ wordname.sym ≠ "LOOPBLOCK"_1

Function isloopblock(s:symbol)boolean name.module.s = "$loopblock"_1 ∧ wordname.s = "LOOPBLOCK"_1

Function Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype)symbol
symbol4(moduleref("internallib $loopblock", resulttype)
, "LOOPBLOCK"_1
, typeref.[toword.firstvar, "."_1, "internallib"_1]
, types
, resulttype
)

Function firstvar(a:symbol)int toint.abstracttypename.first.types.a

Function EqOp symbol symbol(internalmod, "=", typeint, typeint, typeboolean)

Function GtOp symbol symbol(internalmod, ">", typeint, typeint, typeboolean)

Function isblock(s:symbol)boolean name.module.s = "$block"_1

Function iscontinue(s:symbol)boolean name.module.s ∈ "$continue"

Function isSequence(s:symbol)boolean name.module.s = "$sequence"_1

Function isRecord(s:symbol)boolean name.module.s = first."$record"

Function iswordseq(s:symbol)boolean name.module.s = first."$words"

Function isword(s:symbol)boolean name.module.s ∈ "$word"

Function isIntLit(s:symbol)boolean name.module.s ∈ "$int"

Function isRealLit(s:symbol)boolean name.module.s ∈ "$real"

Function isrecordconstant(s:symbol)boolean name.module.s = first."$constant"

Function wordname(s:symbol)word first.worddata.s

Function typebit mytype typeref."bit bits"

Function typebits mytype typeref."bits bits"

Function typebyte mytype typeref."byte bits"

Function typeword mytype typeref."word words"

Function typechar mytype typeref."char standard"

Function packedtypes seq.mytype
[typeref."packed2 tausupport"
, typeref."packed3 tausupport"
, typeref."packed4 tausupport"
, typeref."packed5 tausupport"
, typeref."packed6 tausupport"
]

Function isdecodeword(sym:symbol)boolean sym = symbol(moduleref."words", "decodeword", typeword, typeint)

Function deepcopyseqword symbol
symbol4(moduleref("seq", typeword)
, "type"_1
, seqof.typeword
, [seqof.typeword]
, seqof.typeword
)

Function makerealSymbol symbol symbol(moduleref."real", "makereal", seqof.typeword, typereal)

Function indexsymbol(T:mytype)symbol symbol(moduleref("seq", T), "_", seqof.T, typeint, T)

Function addencodingsymbol(T:mytype)symbol
let encodingstatetype = typeref."encodingstate encoding"
let encodingpairtype = typeref."encodingpair encoding"
symbol(moduleref("encoding", T)
, "add"
, [addabstract(encodingstatetype, T), addabstract(encodingpairtype, T)]
, addabstract(encodingstatetype, T)
)

Function outofboundssymbol symbol symbol(moduleref."tausupport", "outofbounds", seqof.typeword)

Function encodenosym symbol symbol(moduleref."tausupport", "encodingno", seqof.typeword, typeint)

Function blockitsymbol(T:mytype)symbol
{assert isseq.T /and print.parameter.T /in["int", "real", "ptr", "packed2", "packed3", "packed4", "packed5", "packed6 
", "byte"]report"HJK"+print.T}
symbol(moduleref."tausupport", "blockIt", T, T)

_________________

Function isconstantorspecial(s:symbol)boolean isconst.s ∨ isspecial.s

Function Local(i:int)symbol Local(toword.i, typeint, i)

Function Optionsym symbol symbol(internalmod, "option", typeint, seqof.typeword, typeint)

----------------

Function Define(i:int)symbol Define(toword.i, i)

Function Define(name:word, i:int)symbol
symbolZ(moduleref."internallib $define"
, name
, empty:seq.mytype
, empty:seq.mytype
, typeint
, specialbit
, tobits.i
)

Function Fref(s:symbol)symbol
assert not.isconst.s /and first.worddata.s /nin "FREF" report "FREF problem"+print.s
let z = 
 extrabits(types.s
 , worddata.s
 , constbit ∨ frefbit ∨ hashbits.s ∧ hashmask
 )
symbol(worddata.s, module.s, types.s, raw.s, z)

Function basesym(s:symbol)symbol
if isFref.s then
 let flags = hashbits.s ∧ xor(constbit ∨ frefbit ∨ hasfrefbit, tobits.-1)
 let newbits = extrabits(types.s, worddata.s, flags)
 symbol(worddata.s, module.s, types.s, raw.s, newbits)
else s

Function GetSeqLength symbol symbol(internalmod, "getseqlength", typeptr, typeint)

Function GetSeqType symbol symbol(internalmod, "getseqtype", typeptr, typeint)

Function abortsymbol(typ:mytype)symbol
let a = if isseq.typ then typeptr else typ
symbol(builtinmod.a, "assert", seqof.typeword, a)

Function getoption(code:seq.symbol)seq.word
if isempty.code ∨ last.code ≠ Optionsym then empty:seq.word else worddata.code_(length.code - 1)

Function removeoptions(code:seq.symbol)seq.symbol
if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)else code

Function addoption(code:seq.symbol, option:seq.word)seq.symbol
let current = asset.getoption.code
let new = current ∪ asset.option
if cardinality.new = cardinality.current then code
else removeoptions.code + Words.toseq.new + Optionsym

Export typeref(seq.word)mytype

Export moduleref(seq.word, para:mytype)modref

Export moduleref(seq.word)modref

Export addabstract(a:mytype, t:mytype)mytype

Export typeT mytype

Export seqof(mytype)mytype

------

Export type:symbol

Function nametype(sym:symbol)seq.mytype if issimplename.sym then empty:seq.mytype else[first.types.sym]

_______________________________________________

Export type:modref

Export issimple(modref)boolean

Export para(modref)mytype

Export tomodref(mytype)modref

Export name(modref)word

Export library(modref)word

Export isseq(mytype)boolean

Export isencoding(mytype)boolean

Export processof(mytype)mytype

Export abstracttype(mytype)mytype

Export abstracttypename(mytype)word

Export internalmod modref

Export isabstract(modref)boolean

Export types(symbol)seq.mytype

Export ?(typedef, typedef)ordering

Export ?(modref, modref)ordering

Function PreFref symbol symbol(internalmod, "PreFref", typeint)

Function Local(name:word, type:mytype, parano:int)symbol
symbolZ(moduleref."internallib $local"
, name
, empty:seq.mytype
, empty:seq.mytype
, type
, specialbit
, tobits.parano
)

Function modFor(para:mytype)modref moduleref("internallib $for", para)

Function inModFor(sym:symbol)boolean name.module.sym = "$for"_1

Function builtinmod(para:mytype)modref moduleref("internallib builtin", para)

Function isBuiltin(sym:symbol)boolean name.module.sym = "builtin"_1

Function isInternal(sym:symbol)boolean name.module.sym = "internal"_1

Function isGlobal(sym:symbol)boolean name.module.sym = "$global"_1

Export typebase(i:int)mytype

Export print(mytype)seq.word

Export replaceT(mytype, mytype)mytype

Export replaceT(mytype, modref)modref

Export=(mytype, mytype)boolean

Export isseq(mytype)boolean

Function deepcopySym(rt:mytype)symbol
if rt = typereal then symbol(moduleref."tausupport", "deepcopy", typereal, typereal)
else if rt = typeint then symbol(moduleref."tausupport", "deepcopy", typeint, typeint)
else symbol4(replaceT(parameter.rt, abstractModref.rt), "type"_1, rt, [rt], rt)

Function iscore4(typ:mytype)boolean typ = typeint ∨ typ = typereal ∨ typ = typeptr ∨ typ = typeboolean

∨ typ=typebyte

Function setSym(typ:mytype)symbol
let fldtype = 
 if isseq.typ then typeptr else if isencoding.typ then typeint else typ
symbol(if iscore4.fldtype then internalmod else builtinmod.fldtype
, "set"
, typeptr
, fldtype
, typeptr
)

Function Getfld(fldtype:mytype)symbol
let kind2 = 
 if isseq.fldtype then typeptr
 else if isencoding.fldtype ∨ fldtype = typeword then typeint else fldtype
symbol(builtinmod.kind2, "fld", typeptr, typeint, kind2)

Export type:symdef

type symdef is symlist:seq.symbol, paragraphno:int

Function symdef(sym:symbol, code:seq.symbol)symdef symdef([sym] + code, 0)

Function symdef(sym:symbol, code:seq.symbol, p:int)symdef symdef([sym] + code, p)

Function sym(sd:symdef)symbol first.symlist.sd

Function code(sd:symdef)seq.symbol symlist.sd << 1

Export paragraphno(symdef)int

Function ?(a:symdef, b:symdef)ordering sym.a ? sym.b

Function getCode(a:set.symdef, sym:symbol)seq.symbol
let b = lookup(a, symdef(sym, empty:seq.symbol))
if isempty.b then empty:seq.symbol else code.b_1

Function symconst(i:int, hasfref:boolean)symbol
symbol(moduleref."internallib $constant"
, [toword.i]
, empty:seq.mytype
, typeptr
, if hasfref then constbit ∨ hasfrefbit else constbit
)

___________________________

type symbolref is toint:int

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function ?(a:symbolref, b:symbolref)ordering toint.a ? toint.b

Function =(a:symbolref, b:symbolref)boolean toint.a = toint.b

Function symbolref(sym:symbol)symbolref symbolref.addorder.sym

Function assignencoding(a:symbol)int nextencoding.a

Function decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s) 