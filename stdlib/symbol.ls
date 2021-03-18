Module symbol

use bits

use mytype

use standard

use seq.char

use seq.myinternaltype

use otherseq.mytype

use seq.mytype

use seq.programele

use seq.symbol

use set.symbol

use encoding.symbolconstant

use otherseq.word

use set.word

use seq.seq.char

use otherseq.seq.word

use seq.seq.word

Export type:programele

Export type:symbol

Export typeint mytype

Export typeptr mytype

Export addabstract(a:word, b:mytype)mytype

Export type:set.symbol

Export type:mytype

Export mytype(seq.word)mytype

Export abstracttype(m:mytype)word

Export isabstract(a:mytype)boolean

Export parameter(m:mytype)mytype

Export print(p:mytype)seq.word

Export =(t:mytype, b:mytype)boolean

Export replaceT(with:mytype, m:mytype)mytype

Export iscomplex(a:mytype)boolean

Export type:firstpass

Function typerep(m:mytype)seq.word towords.m

/Function abstracttype(w:word, parameter:mytype)mytype mytype(typerep.parameter + w)

Function =(a:symbol, b:symbol)boolean
 flags.a = flags.b ∧ fsig.a = fsig.b ∧ modname.a = modname.b

type symbol is fsig:seq.word, module:seq.word, returntype:seq.word, zcode:seq.symbol, flags:bits

Function extrabits(s:symbol)int toint.flags.s

Function fsighash(s:symbol)int toint(flags.s >> 4)

function extrabits(fsig:seq.word, flags:bits)bits bits.hash.fsig << 4 ∨ flags

Function symbol(fsig:seq.word, module:seq.word, returntype:seq.word)symbol symbol(fsig, module, returntype, empty:seq.symbol)

Function symbol(fsig:seq.word, module:seq.word, returntype:seq.word, zcode:seq.symbol)symbol
 symbol(fsig, module, returntype, zcode, extrabits(fsig, bits.0))

Function symbol(fsig:seq.word, module:seq.word, returntype:seq.word, flag:bits)symbol
 symbol(fsig, module, returntype, empty:seq.symbol, extrabits(fsig, flag))

Export fsig(symbol)seq.word

Function newsymbol(name:seq.word, modname:mytype, paratypes:seq.mytype, resulttype:mytype)symbol
 symbol(if length.paratypes = 0 then name
 else
  name + "("
  + for acc ="", @e = paratypes do list(acc,",", typerep.@e)/for(acc)
  + ")"
 , typerep.modname
 , typerep.resulttype
 , empty:seq.symbol
 )

Function name(s:symbol)seq.word
 if last.fsig.s ∉ ")"then fsig.s
 else break(fsig.s >> 1,"(", false)_1

Function paratypes(s:symbol)seq.mytype
 for acc = empty:seq.mytype, @e = paratypesastext.s do acc + mytype.@e /for(acc)

function paratypesastext(s:symbol)seq.seq.word
let a = fsig.s
 if last.a ≠ ")"_1 then empty:seq.seq.word
 else break(a >> 1,",(", false) << 1

Function modname(s:symbol)mytype mytype.module.s

Function resulttype(s:symbol)mytype mytype.returntype.s

Function nopara(s:symbol)int
 if isconst.s ∨ islocal.s ∨ isparameter.s then 0
 else if isspecial.s ∧ last.module.s ∉ "$record $loopblock"then
  { assert last.module.s in"$continue $block $apply $exitblock $br $record $loopblock $define"report"X"+ module.s }
  if last.module.s = "$define"_1 ∨ isbr.s then 1
  else
   assert length.fsig.s > 1 report"define problem" + fsig.s + module.s + stacktrace
    toint.(fsig.s)_2
 else if last.fsig.s ≠ ")"_1 then 0
 else
  for acc = if last.fsig.s = ")"_1 then 1 else 0 /if, e = fsig.s do
   if","_1 = e then acc + 1 else acc
  /for(acc)

Function ?(a:symbol, b:symbol)ordering
 fsighash.a ? fsighash.b ∧ fsig.a ? fsig.b ∧ module.a ? module.b

Function ?2(a:symbol, b:symbol)ordering fsighash.a ? fsighash.b ∧ fsig.a ? fsig.b

Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
 findelement2(dict, newsymbol(name, mytype."?", types, mytype."?"))

Function lookupfsig(dict:set.symbol, fsig:seq.word)set.symbol findelement2(dict, symbol(fsig,"?","?"))

Function printdict(s:set.symbol)seq.word
 for acc ="", @e = toseq.s do acc + print.@e /for(acc)

type mapele is s:symbol, target:symbol

Export type:mapele

Export s(mapele)symbol

Function key(a:mapele)symbol s.a

Export target(a:mapele)symbol

Function replaceTsymbol2(with:mytype, s:symbol)mapele mapele(replaceTsymbol(with, s), s)

Function replaceTsymbol(with:mytype, s:symbol)symbol
 if with = mytype."T"then s
 else
  let fsig = fsig.s
  let parts = if last.fsig ≠ ")"_1 then [ fsig]else break(fsig >> 1,",(", false)
  let name = parts_1
  let newname = if last.name = "T"_1 then
   name >> 1
   + if typerep.with = ""then""else print.with
  else name
  let newfsig = if length.parts = 1 then newname
  else
   newname + "("
   + for acc ="", @e = parts << 1 do list(acc,",", typerep.replaceT(with, mytype.@e))/for(acc)
   + ")"
   symbol(newfsig, typerep.replaceT(with, modname.s), typerep.replaceT(with, resulttype.s), zcode.s)

Function ?(a:mytype, b:mytype)ordering towords.a ? towords.b

type firstpass is modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unbound:set.symbol, types:seq.myinternaltype, prg:program

Function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.myinternaltype)firstpass
 firstpass(modname, uses, defines, exports, unboundexports, unboundx, types, emptyprogram)

Export firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.myinternaltype, program)firstpass

Export modname(firstpass)mytype

Export defines(firstpass)set.symbol

Export exports(firstpass)set.symbol

Export uses(firstpass)seq.mytype

Export unboundexports(firstpass)seq.symbol

Export unbound(firstpass)set.symbol

Export types(firstpass)seq.myinternaltype

Export prg(firstpass)program

_______________________________

Function Parameter(name:word, type:mytype, parano:int)symbol
 symbol([ name], ["para"_1, toword.parano,"$"_1], towords.type, specialbit)

Function isparameter(s:symbol)boolean
 (module.s)_1 = "para"_1 ∧ last.module.s = "$"_1

Function istypeexport(s:symbol)boolean subseq(fsig.s, 1, 2) = "type:"

Function isIdx(s:symbol)boolean
 last.module.s = "builtin"_1 ∧ (fsig.s)_1 = "IDX"_1

Function Idx(type:mytype)symbol
let kind = abstracttype.type
 if kind = "int"_1 ∨ kind = "byte"_1 then IdxInt
 else if kind = "ptr"_1 then IdxPtr
 else if kind = "boolean"_1 then symbol("IDX:boolean(ptr, int)","boolean builtin","boolean")
 else if kind = "real"_1 then IdxReal
 else
  symbol("IDX:" + print.type + "(ptr, int)", typerep.type + "builtin", typerep.type)

Function seqeletype(type:mytype)mytype
let para = typerep.parameter.type
 mytype.if length.para > 1 ∨ para_1 ∈ "int real boolean"then para
 else if para_1 ∈ "int byte bit"then"int"else"ptr"

Function IdxS(type:mytype)symbol
let para = typerep.parameter.type
 symbol("idxseq(" + para + "seq, int)", para + "builtin", typerep.seqeletype.type)

Function IdxInt symbol symbol("IDX:int(ptr, int)","int builtin","int")

Function IdxReal symbol symbol("IDX:real(ptr, int)","real builtin","real")

Function IdxPtr symbol symbol("IDX:ptr(ptr, int)","ptr builtin","ptr")

Function Callidx(type:mytype)symbol
let t = typerep.parameter.type
 symbol("callidx(" + t + "seq, int)", t + "builtin", typerep.seqeletype.type)

Function packedindex2(type:mytype)seq.symbol
let ds = if length.typerep.type > 2 then"ptr"_1 else(typerep.type)_1
 if ds ∈ "packed2 packed3 packed4 packed5 packed6"then
  [ symbol("packedindex(" + ds + "seq, int)","internal","ptr")]
 else if ds ∈ "byte"then
  [ Lit.-1, PlusOp, symbol("extractbyte(byte seq, int)","internal","int")]
 else [ Lit.-1, PlusOp, symbol("extractbit(bit seq, int)","internal","int")]

function Record(kinds:seq.word)symbol
 symbol("RECORD("
 + for acc ="", e = kinds do list(acc,",", [ e])/for(acc)
 + ")","$record","ptr", specialbit)

Function Record(types:seq.mytype)symbol
 symbol("RECORD("
 + for acc ="", e = types do list(acc,",", typerep.e)/for(acc)
 + ")","$record","ptr", specialbit)

Function Sequence(eletype:mytype, length:int)symbol
 symbol("SEQUENCE" + toword.length, typerep.eletype + "$sequence", typerep.eletype + "seq", specialbit)

Function maybepacked(t:mytype)boolean
 abstracttype.t = "seq"_1 ∧ abstracttype.parameter.t ∈ "byte bit packed2 packed3 packed4 packed5 packed6"

Function continue(i:int)symbol symbol(["CONTINUE"_1, toword.i],"$continue","?", specialbit)

Function Constant2(args:seq.symbol)symbol
 { let args = subseq(argsin, 1, length.argsin-1)}
 let fsig ="CONSTANT" + toword.valueofencoding.encode.symbolconstant.args
  symbol(fsig,"$constant", if isSequence.last.args then returntype.last.args else"ptr", args, extrabits(fsig, constbit))

Function Emptyseq(type:mytype)seq.symbol [ Sequence(type, 0)]

Function isrecordconstant(s:symbol)boolean module.s = "$constant"

function hash(s:seq.symbol)int
 hash.for acc ="", e = s do acc + sigandmodule.e /for(acc)

function assignencoding(a:int, symbolconstant)int a + 1

type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function isconstantorspecial(s:symbol)boolean isconst.s ∨ isspecial.s

function specialbit bits bits.4

function constbit bits bits.1

Function isspecial(s:symbol)boolean(flags.s ∧ specialbit) = specialbit

Function isconst(s:symbol)boolean(flags.s ∧ constbit) = constbit

Function islit(s:symbol)boolean
 module.s = "$int" ∨ module.s = "$real" ∨ module.s = "$boolean"

Function isFref(s:symbol)boolean module.s = "$fref"

function sigandmodule(s:symbol)seq.word fsig.s + module.s

Function Exit symbol symbol("EXITBLOCK 1","$exitblock","?", specialbit)

Function ifthenelse(c:seq.symbol, t:seq.symbol, e:seq.symbol, type:mytype)seq.symbol
 [ start.type] + c + Br2(1, 2) + t + Exit + e + Exit
 + EndBlock

Function Br2(t:int, f:int)symbol
 symbol("BR2:" + toword.t + toword.f + "(boolean)","$br","?", specialbit)

Function start(t:mytype)symbol symbol("/start", typerep.t + "$loopblock", typerep.t, specialbit)

Function EndBlock symbol symbol("BLOCK 0","int $block","int", specialbit)

Function isstartorloop(sym:symbol)boolean last.module.sym ∈ "$loopblock"

Function isstart(sym:symbol)boolean
 last.module.sym = "$loopblock"_1 ∧ (fsig.sym)_1 ≠ "LOOPBLOCK"_1

last.module.sym ="$start"_1

Function isloopblock(s:symbol)boolean
 last.module.s = "$loopblock"_1 ∧ (fsig.s)_1 = "LOOPBLOCK"_1

Function Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype)symbol
let fsig = for acc ="LOOPBLOCK:" + toword.firstvar + "(", t = types do
 acc + typerep.t + ","
/for(acc >> 1 + ")")
 symbol(fsig, typerep.resulttype + "$loopblock", typerep.resulttype, specialbit)

Function firstvar(a:symbol)int toint.(fsig.a)_3

Function brt(s:symbol)int toint.(fsig.s)_3

Function brf(s:symbol)int toint.(fsig.s)_4

Function Local(i:int)symbol Local.toword.i

Function Local(w:word)symbol symbol([ w],"local $","?", specialbit)

Function Local(name:seq.word, type:mytype)symbol symbol(name,"local $", towords.type, specialbit)

Function islocal(s:symbol)boolean module.s = "local $"

Function Reallit(i:int)symbol symbol([ toword.i],"$real","real", constbit)

Function Lit(i:int)symbol symbol([ toword.i],"$int","int", constbit)

Function Littrue symbol symbol("1","$boolean","boolean", constbit)

Function Litfalse symbol symbol("0","$boolean","boolean", constbit)

Function Words(s:seq.word)symbol symbol(s,"$words","word seq", constbit)

Function Word(s:word)symbol symbol([ s],"$word","word", constbit)

Function Define(s:seq.word)symbol Define.s_1

Function Define(w:word)symbol symbol(["DEFINE"_1, w],"$define","?", specialbit)

Function Define(w:int)symbol Define.toword.w

Function Fref(s:symbol)symbol
let fsig ="FREF" + fsig.s + module.s
 symbol(fsig,"$fref","?", [ s], extrabits(fsig, constbit))

Function Optionsym symbol symbol("option(int, word seq)","builtin","?")

/Function STKRECORDOp symbol symbol("STKRECORD(ptr, ptr)","builtin","ptr")

/Function NullptrOp symbol symbol("nullptr","builtin","ptr")

Function isabstractbuiltin(s:symbol)boolean length.module.s > 1 ∧ last.module.s = "builtin"_1

Function EqOp symbol symbol("=(int, int)","standard","boolean")

Function NotOp symbol symbol("not(boolean)","standard","boolean")

Function GtOp symbol symbol(">(int, int)","standard","boolean")

Function PlusOp symbol symbol("+(int, int)","standard","int")

Function MultOp symbol symbol("*(int, int)","standard","int")

Function GetSeqLength symbol symbol("getseqlength(ptr)","tausupport","int")

Function GetSeqType symbol symbol("getseqtype(ptr)","tausupport","int")

Function isinOp(s:symbol)boolean
 fsig.s
 ∈ ["∈(int, int seq)","∈(word, word seq)","=(int, int)","=(word, word)"]

Function isblock(s:symbol)boolean last.module.s = "$block"_1

Function isRecord(s:symbol)boolean module.s = "$record"

Function isSequence(s:symbol)boolean last.module.s = "$sequence"_1

Function iscontinue(s:symbol)boolean module.s = "$continue"

Function isdefine(s:symbol)boolean module.s = "$define"

Function isexit(s:symbol)boolean module.s = "$exitblock"

Function isbr(s:symbol)boolean module.s = "$br"

Function value(s:symbol)int toint.(fsig.s)_1

Function constantcode(s:symbol)seq.symbol
 if isFref.s then zcode.s
 else if isrecordconstant.s then
  if isSequence.last.zcode.s then
   [ Lit.0, Lit.nopara.last.zcode.s] + zcode.s >> 1
  else zcode.s >> 1
 else empty:seq.symbol

Function basesym(s:symbol)symbol if module.s = "$fref"then(zcode.s)_1 else s

Function getoption(code:seq.symbol)seq.word
 if isempty.code ∨ last.code ≠ Optionsym then empty:seq.word else fsig.code_(length.code - 1)

Function removeoptions(code:seq.symbol)seq.symbol
 if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)
 else code

------

Function hash(s:symbol)int toint(flags.s >> 4)

Export type:program

type programele is data:seq.symbol

Function target(a:programele)symbol(data.a)_1

Function code(a:programele)seq.symbol subseq(data.a, 2, length.data.a)

Function isdefined(a:programele)boolean not.isempty.data.a

Function emptyprogram program program2.empty:set.symbol

type program is toset:set.symbol

Function ∪(p:program, a:program)program program(toset.p ∪ toset.a)

Function toseq(p:program)seq.symbol toseq.toset.p

Function ∈(s:symbol, p:program)boolean s ∈ toset.p

Function program2(a:set.symbol)program program.a

Function toseqprogramele(p:program)seq.programele
 for acc = empty:seq.programele, e = toseq.toset.p do acc + programele.zcode.e /for(acc)

Function lookupcode(p:program, s:symbol)programele
let t = findelement(s, toset.p)
 if isempty.t then programele.empty:seq.symbol else programele.zcode.t_1

Function map(p:program, s:symbol, target:symbol, code:seq.symbol)program
 { let t = if isempty.zcode.target then target else symbol(fsig.target, module.target, returntype.target)}
 let sym = symbol(fsig.s, module.s, returntype.s, [ target] + code)
  program.replace(toset.p, sym)

/type program is toset:set.symbol

/Function program2(a:set.symbol)program program(for(s ∈ toseq.a, acc = empty:hashset.symbol)acc + s)

/Function ∪(p:program, a:program)program program(tohashset.p ∪ tohashset.a)

/Function toseq(p:program)seq.symbol toseq.asset.toseq.tohashset.p

/Function ∈(s:symbol, p:program)boolean not.isempty.findelement(s, tohashset.p)

/Function lookupcode(p:program, s:symbol)programele let t = findelement(s, tohashset.p)if isempty.t then programele.empty:seq.symbol else programele.zcode.t_1

Function map(p:program, s:symbol, code:seq.symbol)program map(p, s, s, code)

Function addoption(p:program, s:symbol, option:seq.word)program
let code = code.lookupcode(p, s)
let current = asset.getoption.code
 if current = asset.option then p
 else
  let newcode = removeoptions.code + Words.toseq(current ∪ asset.option) + Optionsym
   map(p, s, newcode)

type typedict is data:seq.myinternaltype

Function +(a:typedict, b:seq.myinternaltype)typedict typedict(data.a + b)

Function print(t:typedict)seq.word
 for acc ="", e = data.t do list(acc," /br", print3.e)/for(acc)

type myinternaltype is kind:word, name:word, modname:mytype, subflds:seq.mytype

Export type:myinternaltype

Export kind(myinternaltype)word

Export name(myinternaltype)word

Export modname(myinternaltype)mytype

Function isdefined(it:myinternaltype)boolean kind.it = "defined"_1

Function typekind(t:myinternaltype)word kind.t

Function modpara(t:myinternaltype)mytype parameter.modname.t

Export subflds(myinternaltype)seq.mytype

function =(a:myinternaltype, b:myinternaltype)boolean
 name.a = name.b ∧ parameter.modname.a = parameter.modname.b

Function changesubflds(t:myinternaltype, subflds:seq.mytype)myinternaltype myinternaltype("defined"_1, name.t, modname.t, subflds)

Export myinternaltype(kind:word, name:word, modname:mytype, subflds:seq.mytype)myinternaltype

Function replaceTmyinternaltype(with:mytype, it:myinternaltype)myinternaltype myinternaltype(kind.it, name.it, replaceT(with, modname.it), subflds.it)

Function tomyinternaltype(s:seq.word)myinternaltype
let t = parseit(s, 1, [ s_1], empty:seq.seq.word)
 myinternaltype(t_2_1, t_3_1, mytype.t_4, for acc = empty:seq.mytype, e = subseq(t, 5, length.t)do acc + mytype.e /for(acc))

function parseit(s:seq.word, i:int, fld:seq.word, flds:seq.seq.word)seq.seq.word
 if i > length.s then flds + fld
 else if s_i = "."_1 then
  parseit(s, i + 2, [ s_(i + 1)] + fld, flds)
 else { end of fld } parseit(s, i + 1, [ s_i], flds + fld)

Function print3(it:myinternaltype)seq.word
 if not.isdefined.it then
  "module:" + print.modname.it + "type" + name.it + "is"
  + kind.it
  + for acc ="", e = subflds.it do list(acc,",", printfld.e)/for(acc)
 else
  [ kind.it, name.it] + print.modname.it
  + for acc ="", e = subflds.it do acc + print.e /for(acc)

function printfld(f:mytype)seq.word [ abstracttype.f,":"_1] + print.parameter.f

Export fsig(symbol)seq.word

Export module(symbol)seq.word

Export returntype(symbol)seq.word

Export type:symbol

Export zcode(symbol)seq.symbol

Function print(f:symbol)seq.word
let module = module.f
let fsig = fsig.f
 if islocal.f ∨ isparameter.f then [ merge(["%"_1] + fsig)]
 else if islit.f then
  if module = "$boolean"then
   if fsig = "0"then"Litfalse"else"Littrue"
  else fsig
 else if module = "$words"then
  if '"'_1 ∈ fsig then"'" + fsig + "'"
  else '"' + fsig + '"'
 else if module = "$word"then"WORD" + fsig
 else if isspecial.f then
  if fsig_1 = "/start"_1 then
   fsig + "(" + print.resulttype.f + ") /br"
  else if fsig_1 = "BLOCK"_1 then"EndBlock  /br"
  else if fsig_1 = "EXITBLOCK"_1 then"Exit  /br"
  else if isbr.f then
   "Br2(" + fsig_3 + "," + fsig_4 + ") /br"
  else if fsig_1 ∈ "BR2 LOOPBLOCK CONTINUE"then fsig + " /br"else fsig
 else if isrecordconstant.f then fsig
 else if isFref.f then"FREF" + print.(constantcode.f)_1
 else if last.fsig = ")"_1 then fsig else fsig + "()"/if
 + print.mytype.module

Function print(p:program, i:symbol)seq.word
let d = lookupcode(p, i)
 if not.isdefined.d then print.i
 else
  print.i + for acc ="", @e = code.d do acc + print.@e /for(acc)

Function printwithoutconstants(p:program, i:symbol)seq.word
let d = lookupcode(p, i)
 if not.isdefined.d then print.i
 else
  print.i
  + for acc ="", @e = removeconstant.code.d do acc + print.@e /for(acc)

Function findelement(d:typedict, type:mytype)seq.myinternaltype
 findelement(myinternaltype("?"_1, abstracttype.type, mytype(towords.parameter.type + "?"), empty:seq.mytype), data.d)

Export typedict(seq.myinternaltype)typedict

Export type:typedict

Function getbasetype(d:typedict, type:mytype)mytype getbasetype(d, type, true)

function getbasetype(d:typedict, type:mytype, top:boolean)mytype
 if abstracttype.type ∈ "packed2 packed3 packed4 packed5 packed6"then typeptr
 else if abstracttype.type ∈ "int boolean real ptr"then type
 else if abstracttype.type = "seq"_1 then
  if abstracttype.parameter.type ∈ "int boolean real ptr bit byte packed2 packed3 packed4 packed5 packed6"then type
  else addabstract("seq"_1, getbasetype(d, parameter.type, false))
 else if type = mytype."internaltype"then typeptr
 else if abstracttype.type = "$base"_1 then { used for type of next in for expression } type
 else
  let t = findelement(d, type)
   assert length.t = 1 report"type not found" + print.type + stacktrace
   let size = length.subflds.t_1
    if size > 1 then
     if top then typeptr
     else if size = 2 then mytype."packed2"
     else if size = 3 then mytype."packed3"
     else if size = 4 then mytype."packed4"
     else if size = 5 then mytype."packed5"
     else if size = 6 then mytype."packed6"else typeptr
    else
     let basetype =(subflds.t_1)_1
      if abstracttype.basetype = "seq"_1 then getbasetype(d, basetype, true)else basetype

Function getsubflds(d:typedict, type:mytype)seq.mytype
 if type = typeint ∨ type = mytype."real" ∨ type = typeptr then [ type]
 else
  { if type = mytype."boolean"then typeinfo.[ mytype."boolean"]else }
  if abstracttype.type = "seq"_1 ∨ type = mytype."internaltype"then [ typeptr]
  else
   let t = findelement(d, type)
    assert length.t = 1 report"type not found" + print.type + stacktrace
     subflds.t_1

Function buildargcode(alltypes:typedict, sym:symbol)int
 { needed because the call interface implementation for reals is different than other types is some implementations }
 for acc = 1, typ = paratypes.sym + resulttype.sym do
  acc * 2
  + if getbasetype(alltypes, typ) = mytype."real"then 1 else 0
 /for(acc)

Function typesym(it:myinternaltype)symbol
let t = addabstract(name.it, parameter.modname.it)
 newsymbol("type:" + print.t, modname.it, [ t], t)

Function deepcopysym(d:typedict, type:mytype)symbol typesym(d, type)

Function typesym(d:typedict, type:mytype)symbol
 if type = typeint then symbol("deepcopy(int)","tausupport","int")
 else if type = mytype."real"then symbol("deepcopy(real)","tausupport","real")
 else
  let e = findelement(d, type)
   assert length.e = 1 report"type not found" + print.type + stacktrace
   let it = e_1
   let t = addabstract(name.it, parameter.modname.it)
    newsymbol("type:" + print.t, modname.it, [ t], t)

Function deepcopysym(dict:set.symbol, type:mytype)set.symbol
 if type ∈ [ typeint, mytype."real"]then asset.[ typesym(typedict.empty:seq.myinternaltype, type)]
 else lookup(dict,"type:" + print.type, [ type])

Function removeconstant(s:seq.symbol)seq.symbol
 for acc = empty:seq.symbol, @e = s do
  acc + if isrecordconstant.@e then removeconstant.zcode.@e else [ @e]
 /for(acc)

_______________________________________________

Function print(s:seq.symbol)seq.word
 for acc ="", e = s do
  acc + { if last.module.e ∈"$branch $exit2 $start"then fsig.e + EOL else } print.e
 /for(acc)

___________________________________________________________

module hashset.T

use bits

use standard

use seq.T

use otherseq.seq.T

use seq.seq.T

type hashset is table:seq.seq.T, cardinality:int, mask:bits

unbound hash(T)int

unbound =(T, T)boolean

Function ∪(a:hashset.T, b:hashset.T)hashset.T
 if cardinality.b > cardinality.a then b ∪ a
 else for acc = a, e = toseq.b do acc + e /for(acc)

function clean(s:seq.T, mask:bits, idx:int)seq.T
let currenthash = tobits(idx - 1)
 for acc = empty:seq.T, e = s do
  if e ∈ acc ∨ (tobits.hash.e ∧ mask) ≠ currenthash then acc else acc + e
 /for(acc)

Function +(s:hashset.T, a:T)hashset.T
let idx = toint(tobits.hash.a ∧ mask.s) + 1
 assert between(idx, 1, length.table.s)report"XXX" + print.idx + print.length.table.s + print.mask.s
 let list =(table.s)_idx
 let t = replace(table.s, idx, clean([ a] + list, mask.s, idx))
  assert not.isempty.clean([ a] + list, mask.s, idx)report"XX"
   if a ∈ list then hashset(t, cardinality.s, mask.s)
   else
    let newmask = bits.-1 >> (64 - floorlog2((cardinality.s + 1) * 3 / 2))
     if toint.newmask ≤ toint.mask.s then hashset(t, cardinality.s + 1, mask.s)
     else hashset(t + t, cardinality.s + 1, mask.s << 1 ∨ 0x1)

Function findelement(ele:T, s:hashset.T)seq.T
let idx = toint(tobits.hash.ele ∧ mask.s) + 1
 findelement(ele,(table.s)_idx)

Function toseq(s:hashset.T)seq.T
 for acc = empty:seq.T, idx = 1, e = table.s do
  next(acc + clean(e, mask.s, idx), idx + 1)
 /for(acc)

Function empty:hashset.T hashset.T hashset([ empty:seq.T, empty:seq.T, empty:seq.T, empty:seq.T], 0, 0x3)

Export type:hashset.T

Export cardinality(hashset.T)int