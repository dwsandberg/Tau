Module symbol

use bits

use seq.seq.char

use seq.char

use seq.myinternaltype

use otherseq.mytype

use seq.mytype

use mytype

use standard

use seq.symbol

use set.symbol

use encoding.symbolconstant

use otherseq.word

use otherseq.seq.word

use seq.seq.word

use set.word

Export type:programele

Export type:symbol

Export typeint mytype

Export typeint mytype

Export typeseq mytype

Export typeptr mytype

Export typeencoding mytype

Export typeencodingstate mytype

Export typeencodingpair mytype

Export typeprocess mytype

Export +(a:mytype, b:mytype)mytype

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

Function abstracttype(w:word, parameter:mytype)mytype mytype(typerep.parameter + w)

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
 symbol(if length.paratypes = 0 then name
 else
  name + "(" + paratypes @ list("",",", typerep.@e) + ")"
 , typerep.modname
 , typerep.resulttype
 , empty:seq.symbol)

Function name(s:symbol)seq.word subseq(fsig.s, 1, findindex("("_1, fsig.s) - 1)

Function paratypes(s:symbol)seq.mytype paratypesastext.s @ +(empty:seq.mytype, mytype.@e)

function paratypesastext(s:symbol)seq.seq.word
 let a = fsig.s
  if length.a < 4 then empty:seq.seq.word
  else
   break(","_1, subseq(a, 1, length.a - 1), findindex("("_1, a) + 1)

Function modname(s:symbol)mytype mytype.module.s

Function resulttype(s:symbol)mytype mytype.returntype.s

Function nopara(s:symbol)int
 if isconst.s ∨ islocal.s then 0
 else if isspecial.s ∧ last.module.s ∉ "$record $loopblock"then
 // assert last.module.s in"$continue $block $apply $exitblock $br $record $loopblock $define"report"X"+ module.s //
  if last.module.s = "$define"_1 then 1 else toint.(fsig.s)_2
 else
  fsig.s
  @ counttrue(if last.fsig.s = ")"_1 then 1 else 0,","_1 = @e)

function counttrue(i:int, b:boolean)int if b then i + 1 else i

Function ?(a:symbol, b:symbol)ordering
 fsighash.a ? fsighash.b ∧ fsig.a ? fsig.b ∧ module.a ? module.b

Function ?2(a:symbol, b:symbol)ordering fsighash.a ? fsighash.b ∧ fsig.a ? fsig.b

Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
 findelement2(dict, newsymbol(name, mytype."?", types, mytype."?"))

Function lookupfsig(dict:set.symbol, fsig:seq.word)set.symbol findelement2(dict, symbol(fsig,"?","?"))

Function printdict(s:set.symbol)seq.word toseq.s @ +("", print.@e)

type mapele is record s:symbol, target:symbol

Export type:mapele

Export s(mapele)symbol

Function key(a:mapele)symbol s.a

Export target(a:mapele)symbol

function replaceT(with:seq.word, s:word)seq.word if"T"_1 = s then with else [ s]

Function replaceT(with:seq.word, s:seq.word)seq.word s @ +("", replaceT(with, @e))

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

Export firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.myinternaltype, program)firstpass

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

Function istypeexport(s:symbol)boolean subseq(fsig.s, 1, 2) = "type:"

Function isIdx(s:symbol)boolean isbuiltin.module.s ∧ (fsig.s)_1 ∈ "IDX"

Function Idx(kind:word)symbol symbol("IDX(T seq, int)", [ kind] + "builtin","T")

Function Callidx(kind:word)symbol
 let t = if kind ∈ "int real"then [ kind]else"ptr"
  symbol("callidx3( T  seq, int)", t + "builtin", t)

 
Function Emptyseq seq.symbol [ Stdseq, Lit.0, symbol("RECORD(int, int)","$record","ptr", specialbit)]

Function Stdseq symbol Lit.0

Function Record(kinds:seq.word)symbol
 symbol("RECORD(" + kinds @ list("",",", [ @e]) + ")","$record","ptr", specialbit)

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

function hash(s:seq.symbol)int hash(s @ +("", sigandmodule.@e))

function assignencoding(a:int, symbolconstant)int a + 1

type symbolconstant is record toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function isconstantorspecial(s:symbol)boolean isconst.s ∨ isspecial.s

Function isnocall(sym:symbol)boolean isconst.sym ∨ isspecial.sym ∨ module.sym = "builtin"

function specialbit bits bits.4

function constbit bits bits.1

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

Function Define(s:seq.word)symbol Define.s_1

Function Define(w:word)symbol symbol(["DEFINE"_1, w],"$define","?", specialbit)

Function Define(w:int)symbol Define.toword.w

Function Fref(s:symbol)symbol
 let fsig ="FREF" + fsig.s + module.s
  symbol(fsig,"$fref","?", [ s], extrabits(fsig, constbit))

Function Optionsym symbol symbol("option(T, word seq)","builtin","?")

Function EqOp symbol symbol("=(int, int)","builtin","boolean")

Function NotOp symbol symbol("not(boolean)","builtin","boolean")

Function GtOp symbol symbol(">(int, int)","builtin","boolean")
 
Function PlusOp symbol symbol("+(int, int)","builtin","int")

Function isinOp(s:symbol)boolean
 fsig.s
 ∈ ["∈(int, int seq)","∈(word, word seq)","in(int, int seq)","in(word, word seq)","=(int, int)","=(word, word)"]

Function isblock(s:symbol)boolean last.module.s = "$block"_1

Function isrecord(s:symbol)boolean module.s = "$record"

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
 if length.code = 0 ∨ last.code ≠ Optionsym then""
 else fsig.code_(length.code - 1)

------

type program is record toset:set.symbol

Function ∩(p:program, a:set.symbol)program program(toset.p ∩ a)

Function ∪(p:program, a:program)program program(toset.p ∪ toset.a)

Export toset(p:program)set.symbol

Export program(set.symbol)program

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
 if last.code ≠ Optionsym then empty:seq.word else fsig.code_(length.code - 1)

Function isbuiltin(a:seq.word)boolean a = "builtin"

Function isbuiltin(a:mytype)boolean isbuiltin.towords.a

type typedict is record data:seq.myinternaltype

Function +(a:typedict, b:seq.myinternaltype)typedict typedict(data.a + b)

Function print(t:typedict)seq.word data.t @ list(""," &br", print3.@e)

type myinternaltype is record kind:word, name:word, modname:mytype, subflds:seq.mytype

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
  myinternaltype(t_2_1, t_3_1, mytype.t_4, subseq(t, 5, length.t) @ +(empty:seq.mytype, mytype.@e))

function parseit(s:seq.word, i:int, fld:seq.word, flds:seq.seq.word)seq.seq.word
 if i > length.s then flds + fld
 else if s_i = "."_1 then
 parseit(s, i + 2, [ s_(i + 1)] + fld, flds)
 else // end of fld // parseit(s, i + 1, [ s_i], flds + fld)

Function print3(it:myinternaltype)seq.word
 if not.isdefined.it then
 "module:" + print.modname.it + "type" + name.it + "is"
  + kind.it
  + subflds.it @ list("",",", printfld.@e)
 else
  [ kind.it, name.it] + print.modname.it
  + subflds.it @ +("", print.@e)

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
  if '"'_1 ∈ fsig then"'" + fsig + "'"
   else '"' + fsig + '"'
  else if module = "$word"then"WORD" + fsig
  else if isspecial.f then
  if fsig_1 ∈ "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then fsig + " &br"else fsig
  else if module = "$constant"then fsig
  else if isFref.f then"FREF" + print.(constantcode.f)_1
  else
   (if last.fsig = ")"_1 then fsig else fsig + "()") + print.mytype.module

Function print(p:program, i:symbol)seq.word
 let d = lookupcode(p, i)
  if not.isdefined.d then print.i else print.i + code.d @ +("", print.@e)

Function printwithoutconstants(p:program, i:symbol)seq.word
 let d = lookupcode(p, i)
  if not.isdefined.d then print.i
  else print.i + removeconstant.code.d @ +("", print.@e)

type typeinfo is record subflds:seq.mytype

Function kind(t:typeinfo)word
 let z = subflds.t
  if length.z > 1 ∨ abstracttype.z_1 = "seq"_1 then"ptr"_1
  else
   let k =(typerep.z_1)_1
    assert k ∈ "int real ptr"report"unexpected fld in internal type" + z @ +("", print.@e) + stacktrace
     // x // k

Export subflds(typeinfo)seq.mytype

Function size(t:typeinfo)int length.subflds.t

Export type:typeinfo

Function findelement(d:typedict, type:mytype)seq.myinternaltype
 findelement(myinternaltype("?"_1, abstracttype.type, mytype(towords.parameter.type + "?"), empty:seq.mytype), data.d)

Export typedict(seq.myinternaltype)typedict

Export type:typedict

Function gettypeinfo(d:typedict, type:mytype)typeinfo
 if type = typeint then typeinfo.[ typeint]
 else if type = mytype."real"then typeinfo.[ mytype."real"]
 else if abstracttype.type = "seq"_1 ∨ type = mytype."internaltype" ∨ type = typeptr then
 typeinfo.[ typeptr]
 else
  let t = findelement(d, type)
   assert length.t = 1 report"type not found" + print.type + stacktrace
    typeinfo.subflds.t_1

Function typesym(it:myinternaltype)symbol
 let t = abstracttype(name.it, parameter.modname.it)
  newsymbol("type:" + print.t, modname.it, [ t], t)

Function deepcopysym(d:typedict, type:mytype)symbol typesym(d, type)

Function typesym(d:typedict, type:mytype)symbol
 if type = typeint then symbol("deepcopy(int)","tausupport","int")
 else if type = mytype."real"then symbol("deepcopy(real)","tausupport","real")
 else
  let e = findelement(d, type)
   assert length.e = 1 report"type not found" + print.type + stacktrace
   let it = e_1
   let t = abstracttype(name.it, parameter.modname.it)
    newsymbol("type:" + print.t, modname.it, [ t], t)

Function deepcopysym(dict:set.symbol, type:mytype)set.symbol
 if type ∈ [ typeint, mytype."real"]then asset.[ typesym(typedict.empty:seq.myinternaltype, type)]
 else lookup(dict,"type:" + print.type, [ type])

Function removeconstant(s:seq.symbol)seq.symbol s @ +(empty:seq.symbol, removeconstant.@e)

function removeconstant(s:symbol)seq.symbol if module.s = "$constant"then removeconstant.zcode.s else [ s]