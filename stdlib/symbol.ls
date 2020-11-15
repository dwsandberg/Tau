Module symbol

use bits

use seq.seq.char

use seq.char

use mangle

use seq.myinternaltype

use otherseq.mytype

use seq.mytype

use mytype

use stacktrace

use stdlib

use seq.symbol

use set.symbol

use encoding.symbolconstant

use otherseq.word

use otherseq.seq.word

use seq.seq.word

use set.word

Export type:programele

Export type:symbol

Export typeint  mytype  

Export typeint  mytype  

Export typeseq  mytype  

Export typeptr  mytype  

Export typepseq  mytype  

Export typeencoding  mytype 

Export typeencodingstate  mytype  

Export typeencodingpair mytype   

Export typeprocess mytype  

Export +(a:mytype,b:mytype) mytype

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

Function typerep(m:mytype) seq.word towords.m

Function abstracttype(w:word,parameter:mytype) mytype mytype(typerep.parameter+w)

Function =(a:symbol, b:symbol)boolean
 flags.a = flags.b ∧ fsig.a = fsig.b ∧ modname.a = modname.b

type symbol is record fsig:seq.word, module:seq.word, returntype:seq.word, zcode:seq.symbol, flags:bits

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
 let b = length.towords.modname > 1 ∧ not((towords.modname)_1 = "T"_1)
 ∧ not.ispara.modname
 let paratyps = if b then @(+, replaceT(parameter.modname), empty:seq.mytype, paratypes)else paratypes
 let sym = symbol(if length.paratyps = 0 then name
 else name + "(" + @(seperator.",", towords,"", paratyps) + ")", towords.modname, towords.if b then replaceT(parameter.modname, resulttype)else resulttype, empty:seq.symbol)
  sym

Function name(s:symbol)seq.word
 let j = findindex("("_1, fsig.s)
  if j > length.fsig.s then fsig.s else subseq(fsig.s, 1, j - 1)

Function paratypes(s:symbol)seq.mytype @(+, mytype, empty:seq.mytype, paratypesastext.s)

function paratypesastext(s:symbol)seq.seq.word
 let a = fsig.s
  if length.a < 4 then empty:seq.seq.word
  else
   break(","_1, subseq(a, 1, length.a - 1), findindex("("_1, a) + 1)

Function modname(s:symbol)mytype mytype.module.s

Function resulttype(s:symbol)mytype mytype.returntype.s

Function nopara(s:symbol)int
 if isconst.s ∨ islocal.s then 0
 else if isspecial.s ∧ not(last.module.s in "$record $loopblock")then
 // assert last.module.s in"$continue $block $apply $exitblock $br $record $loopblock $define"report"X"+ module.s //
  if last.module.s = "$define"_1 then 1 else toint.(fsig.s)_2
 else
  @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

function counttrue(i:int, b:boolean)int if b then i + 1 else i

Function ?(a:symbol, b:symbol)ordering
 fsighash.a ? fsighash.b ∧ fsig.a ? fsig.b ∧ module.a ? module.b

Function ?2(a:symbol, b:symbol)ordering fsighash.a ? fsighash.b ∧ fsig.a ? fsig.b

Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
 findelement2(dict, newsymbol(name, mytype."?", types, mytype."?"))

Function lookupfsig(dict:set.symbol, fsig:seq.word)set.symbol findelement2(dict, symbol(fsig,"?","?"))

Function printdict(s:set.symbol)seq.word @(+, print,"", toseq.s)

type mapele is record s:symbol, target:symbol

Export type:mapele

Export s(mapele)symbol

Function key(a:mapele)symbol s.a

Export target(a:mapele)symbol

function replaceT(with:seq.word, s:word)seq.word if"T"_1 = s then with else [ s]

Function replaceT(with:seq.word, s:seq.word)seq.word @(+, replaceT.with,"", s)

Function replaceTsymbol2(with:mytype, s:symbol)mapele mapele(replaceTsymbol(with, s), s)

Function replaceTsymbol(with:mytype, s:symbol)symbol
 if with = mytype."T"then s
 else
  let newfsig =
  let j = findindex("("_1, fsig.s)
   replaceT(if towords.with = ""then""else print.with, subseq(fsig.s, 1, j - 1))
   + replaceT(towords.with, subseq(fsig.s, j, length.fsig.s))
   symbol(newfsig, replaceT(towords.with, module.s), replaceT(towords.with, returntype.s), zcode.s)

Function ?(a:mytype, b:mytype)ordering towords.a ? towords.b



type firstpass is record modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unbound:set.symbol, types:seq.myinternaltype, prg:program

Function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.myinternaltype)firstpass
 firstpass(modname, uses, defines, exports, unboundexports, unboundx, types, emptyprogram)

Function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.myinternaltype, program)firstpass
 export

Function exportmodule(firstpass)boolean false

Export modname(firstpass)mytype

Export defines(firstpass)set.symbol

Export exports(firstpass)set.symbol

Export uses(firstpass)seq.mytype

Export unboundexports(firstpass)seq.symbol

Export unbound(firstpass)set.symbol

Export types(firstpass)seq.myinternaltype

Export prg(firstpass)program

_______________________________

Export program(s:set.symbol)program

---------------

Function Parameter(name:word, type:mytype, parano:int)symbol
 symbol([ name], ["para"_1, toword.parano,"$"_1], towords.type, specialbit)

function ispara(s:mytype)boolean
 (towords.s)_1 = "para"_1 ∧ last.towords.s = "$"_1

Function deepcopysym(type:mytype)symbol
 symbol("deepcopy(" + towords.type + ")", towords.type + "builtin", towords.type)

Function isIdx(s:symbol)boolean isbuiltin.module.s ∧ (fsig.s)_1 in "IDX"

Function Idx(kind:word)symbol
 let t = if kind in "int real"then [ kind]else"ptr"
  if t = "int"then symbol("IDX(int seq, int)","builtin","int")
  else if t = "real"then symbol("IDX(real seq, int)","builtin","real")
  else symbol("IDX(ptr seq, int)","builtin","ptr")

Function Callidx(kind:word)symbol
 let t = if kind in "int real"then [ kind]else"ptr"
  symbol("callidx(" + t + "seq, int)","builtin", t)

Function Emptyseq seq.symbol [ Lit.0, Lit.0, symbol("RECORD(int, int)","$record","ptr", specialbit)]

Function pseqidxsym(type:mytype)symbol
 newsymbol("_",  typeseq+  type  , [ typepseq+type  , typeint], type)

Function Sequence(len:int, typ:seq.word)symbol
 Record([ typeint, typeint] + constantseq(len, mytype.typ))

Function Record(types:seq.mytype)symbol
 symbol("RECORD(" + @(seperator.",", towords,"", types) + ")","$record","ptr", specialbit)

Function Apply(i:int, basetype:seq.word, returntype:seq.word)symbol
 symbol(["APPLY"_1, toword.i], basetype + "$apply", returntype, specialbit)
 
Function Apply(i:int, basetype:mytype, returntype:mytype)symbol
 symbol(["APPLY"_1, toword.i], towords.basetype + "$apply", towords.returntype, specialbit)

Function Block(type:mytype, i:int)symbol
 symbol("BLOCK" + toword.i, towords.type + "$block", towords.type, specialbit)

function bpara(i:int, result:seq.word)seq.word
 if i = 1 then result else bpara(i - 1, result + ", ?")

Function Loopblock(types:seq.word)symbol symbol("LOOPBLOCK(" + types,"$loopblock","?", specialbit)

Function continue(i:int)symbol symbol(["CONTINUE"_1, toword.i],"$continue","?", specialbit)

Function Constant2(args:seq.symbol)symbol
 // let args = subseq(argsin, 1, length.argsin-1)//
 let fsig ="CONSTANT" + toword.valueofencoding.encode.symbolconstant.args
  symbol(fsig,"$constant","ptr", args, extrabits(fsig, constbit))

Function isrecordconstant(s:symbol)boolean module.s = "$constant"

function hash(s:seq.symbol)int hash.@(+, sigandmodule,"", s)

function assignencoding(a:int, symbolconstant)int a + 1

type symbolconstant is record toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function isconstantorspecial(s:symbol)boolean isconst.s ∨ isspecial.s

Function isnocall(sym:symbol)boolean isconst.sym ∨ isspecial.sym ∨ module.sym = "builtin"

function specialbit bits bits.4

function constbit bits bits.1

function =(a:bits, b:bits)boolean toint.a = toint.b

Function isspecial(s:symbol)boolean(flags.s ∧ specialbit) = specialbit

Function isconst(s:symbol)boolean(flags.s ∧ constbit) = constbit

Function islit(s:symbol)boolean module.s = "$int" ∨ module.s = "$real"

Function isFref(s:symbol)boolean module.s = "$fref"

function sigandmodule(s:symbol)seq.word fsig.s + module.s

Function Exit symbol symbol("EXITBLOCK 1","$exitblock","?", specialbit)

Function Br symbol symbol("BR 3","$br","?", specialbit)

Function Local(i:int)symbol Local.toword.i

Function Local(w:word)symbol symbol([ w],"local $","?", specialbit)

Function Local(name:seq.word, type:mytype)symbol symbol(name,"local $", towords.type, specialbit)

Function islocal(s:symbol)boolean module.s = "local $"

Function Reallit(i:int)symbol symbol([ toword.i],"$real","real", constbit)

Function Lit(i:int)symbol symbol([ toword.i],"$int","int", constbit)

Function Lit0 symbol symbol("0","$int","int", constbit)

Function Words(s:seq.word)symbol symbol(s,"$words","word seq", constbit)

Function Word(s:word)symbol symbol([ s],"$word","word", constbit)

Function Define(s:seq.word)symbol symbol("DEFINE" + s,"$define","?", specialbit)

Function Define(w:word)symbol symbol(["DEFINE"_1, w],"$define","?", specialbit)

Function Fref(s:symbol)symbol
 let fsig ="FREF" + fsig.s + module.s
  symbol(fsig,"$fref","?", [ s], extrabits(fsig, constbit))

Function Optionsym symbol symbol("option(T, word seq)","builtin","?")

Function EqOp symbol symbol("=(int, int)","builtin","boolean")

Function PlusOp symbol symbol("+(int, int)","builtin","int")

Function isinOp(s:symbol)boolean
 fsig.s
 in ["in(int, int seq)","in(word, word seq)","=(int, int)","=(word, word)"]

Function isblock(s:symbol)boolean last.module.s = "$block"_1

Function isrecord(s:symbol)boolean module.s = "$record"

Function isapply(s:symbol)boolean last.module.s = "$apply"_1

Function isloopblock(s:symbol)boolean module.s = "$loopblock"

Function iscontinue(s:symbol)boolean module.s = "$continue"

Function isdefine(s:symbol)boolean module.s = "$define"

Function isexit(s:symbol)boolean module.s = "$exitblock"

Function isbr(s:symbol)boolean module.s = "$br"

Function value(s:symbol)int toint.(fsig.s)_1

Function constantcode(s:symbol)seq.symbol
 if isFref.s then zcode.s
 else if isrecordconstant.s then subseq(zcode.s, 1, length.zcode.s - 1)else empty:seq.symbol

Function basesym(s:symbol)symbol if module.s = "$fref"then(zcode.s)_1 else s

Function options(code:seq.symbol)seq.word
 if length.code = 0 ∨ not(last.code = Optionsym)then""
 else fsig.code_(length.code - 1)

------

type program is record toset:set.symbol

Function ∩(p:program, a:set.symbol)program program(toset.p ∩ a)

Function ∪(p:program, a:program)program program(toset.p ∪ toset.a)

Export toset(p:program)set.symbol

Export program(set.symbol) program

Export type:program

type programele is record data:seq.symbol

Function target(a:programele)symbol(data.a)_1

Function code(a:programele)seq.symbol subseq(data.a, 2, length.data.a)

Function isdefined(a:programele)boolean not.isempty.data.a

Function emptyprogram program program.empty:set.symbol

Function lookupcode(p:program, s:symbol)programele
 let t = findelement(s, toset.p)
  if isempty.t then programele.empty:seq.symbol else programele.zcode.t_1

Function map(p:program, s:symbol, target:symbol, code:seq.symbol)program
 program.replace(toset.p, symbol(fsig.s, module.s, returntype.s, [ target] + code))

Function map(p:program, s:symbol, code:seq.symbol)program map(p, s, s, code)

Function addoption(p:program, s:symbol, option:seq.word)program
 let code = code.lookupcode(p, s)
 let current = asset.getoption.code
  if current = asset.option then p
  else
   let newcode = code + Words.toseq(current ∪ asset.option) + Optionsym
    map(p, s, newcode)

Function getoption(code:seq.symbol)seq.word
 if not(last.code = Optionsym)then empty:seq.word else fsig.code_(length.code - 1)

Function isbuiltin(a:seq.word)boolean a = "builtin"

Function isbuiltin(a:mytype)boolean isbuiltin.towords.a

Function processOption(p:program, t:seq.word)program
 if length.t < 4 ∨ not(t_1 = "*"_1)
 ∨ not(t_2 in "PROFILE INLINE STATE NOINLINE")then
 p
 else
  let modend = findindex(":"_1, t, 3)
  let nameend = findindex("("_1, t, modend + 1)
  let paraend = findindex(")"_1, t, nameend + 1)
  let modname =(gettypelist.subseq(t, 3, modend - 1))_1
  let name =(gettypelist.subseq(t, modend + 1, nameend - 1))_1_1
  let b = subseq(t, nameend + 1, paraend - 1)
  let args = if b = ""then empty:seq.seq.word else gettypelist.subseq(t, nameend + 1, paraend - 1)
  let ret =(gettypelist.subseq(t, paraend + 1, length.t))_1
  let sym = symbol([ name] + "(" + @(seperator.",", identity,"", args) + ")", modname, ret)
  let r = lookupcode(p, sym)
   if isbuiltin.modname then map(p, sym, [ Words.[ t_2], Optionsym])
   else
    assert isdefined.r report"Option problem" + t
     addoption(p, sym, [ t_2])

/function printastype(s:seq.word)seq.word if length.s = 1 then s else [ last.s,"."_1]+ printastype.subseq(s, 1, length.s-1)

function gettypelist(s:seq.word)seq.seq.word gettype(s, 1,"", empty:seq.seq.word)

Function parsetype(s:seq.word)mytype mytype.gettype(s, 1, empty:seq.word, empty:seq.seq.word)_1

function gettype(s:seq.word, i:int, result:seq.word, l:seq.seq.word)seq.seq.word
 if i > length.s then l + result
 else if s_i = ","_1 then gettype(s, i + 1,"", l + result)
 else
  let j = if i < length.s ∧ s_(i + 1) = "."_1 then
  i + 2
  else i + 1
   gettype(s, j, [ s_i] + result, l)

type typedict is record data:seq.myinternaltype

Function +(a:typedict, b:seq.myinternaltype)typedict typedict(data.a + b)

Function print(t:typedict)seq.word @(seperator." &br", towords,"", data.t)

type myinternaltype is record kind:word, name:word, modname:mytype, subflds:seq.mytype

Export type:myinternaltype

Export kind(myinternaltype) word

Export name(myinternaltype) word

Export modname(myinternaltype) mytype

Function isdefined(it:myinternaltype)boolean kind.it="defined"_1

Function  typekind(t:myinternaltype)word kind.t


Function modpara(t:myinternaltype) mytype parameter.modname.t

Export subflds(myinternaltype)seq.mytype

function =(a:myinternaltype, b:myinternaltype)boolean
 name.a = name.b ∧ parameter.modname.a = parameter.modname.b


Function changesubflds(t:myinternaltype,subflds:seq.mytype) myinternaltype
myinternaltype("defined"_1,name.t, modname.t,subflds)

Export myinternaltype( kind:word, name:word, modname:mytype, subflds:seq.mytype ) myinternaltype

Function replaceTmyinternaltype(with:mytype, it:myinternaltype)myinternaltype 
myinternaltype( kind.it, name.it, replaceT(with, modname.it), subflds.it)

Function towords(it:myinternaltype)seq.word
 [  kind.it, name.it] + print.modname.it + @(+, print,"", subflds.it)

Function tomyinternaltype(s:seq.word)myinternaltype
 let t = parseit(s, 1, [ s_1], empty:seq.seq.word)
  myinternaltype( t_2_1, t_3_1, mytype.t_4, @(+, mytype, empty:seq.mytype, subseq(t, 5, length.t)))

function parseit(s:seq.word, i:int, fld:seq.word, flds:seq.seq.word)seq.seq.word
 if i > length.s then flds + fld
 else if s_i = "."_1 then
 parseit(s, i + 2, [ s_(i + 1)] + fld, flds)
 else // end of fld // parseit(s, i + 1, [ s_i], flds + fld)

Function print3(it:myinternaltype)seq.word
 if not.isdefined.it   then
 "module:" + print.modname.it + "type" + name.it + "is"
  + kind.it
  + @(seperator.",", printfld,"", subflds.it)
 else
  [  kind.it, name.it] + print.modname.it + @(+, print,"", subflds.it)

function printfld(f:mytype)seq.word [ abstracttype.f,":"_1] + print.parameter.f

Export fsig(symbol)seq.word

Export module(symbol)seq.word

Export returntype(symbol)seq.word

Export type:symbol

Export zcode(symbol)seq.symbol

Function print(f:symbol)seq.word
 let module = module.f
 let fsig = fsig.f
  if islocal.f ∨ ispara.mytype.module.f then [ merge(["%"_1] + fsig)]
  else if islit.f then fsig
  else if module = "$words"then
  if '"'_1 in fsig then"'" + fsig + "'"
   else '"' + fsig + '"'
  else if module = "$word"then"WORD" + fsig
  else if isspecial.f then
  if fsig_1 in "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then fsig + " &br"else fsig
  else if module = "$constant"then fsig
  else if isFref.f then"FREF" + print.(constantcode.f)_1
  else
   (if last.fsig = ")"_1 then fsig else fsig + "()") + print.mytype.module

Function print(p:program, i:symbol)seq.word
 let d = lookupcode(p, i)
  if not.isdefined.d then print.i else print.i + @(+, print,"", code.d)

type typeinfo is record subflds:seq.mytype

Function kind(t:typeinfo)word
 let z = subflds.t
  if length.z > 1 ∨ abstracttype.z_1 = "seq"_1 then"ptr"_1
  else
   assert(towords.z_1)_1 in "int real ptr"report"unexpected fld in internal type" + @(+, print,"", z)+stacktrace // x //
    (towords.z_1)_1
    
    use stacktrace

Export subflds(typeinfo)seq.mytype

Function size(t:typeinfo)int length.subflds.t

Export type:typeinfo

Function findelement(d:typedict, type:mytype)seq.myinternaltype
 findelement(myinternaltype("?"_1, abstracttype.type, mytype(towords.parameter.type + "?"), empty:seq.mytype), data.d)

Export typedict(seq.myinternaltype)typedict

Export type:typedict

Function gettypeinfo(d:typedict, type:mytype)typeinfo
 if type=typeint then typeinfo.[typeint]
 else if type=mytype."real" then typeinfo.[mytype."real"]
 else if abstracttype.type = "seq"_1 then typeinfo.[ type]
 else if type = mytype."internaltype" &or type= typeptr then typeinfo.[ typeptr]
 else
  let t = findelement(d, type)
   assert length.t = 1 report"type not found" + print.type + stacktrace
    typeinfo.subflds.t_1