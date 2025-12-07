Module symbol1

use seq.modExports

use mytype

use seq.mytype

use standard

use seq1.symbol

use symbol

use symbolconstant

use set.symdef

use typedict

Function nodeLabel(node:symbol) seq.seq.word
{used in drawing graphs}
["", [name.node], %.node]

Function symbol(module:modref, name:seq.word, returntype:mytype) symbol
symbol(module, name, empty:seq.mytype, returntype)

Export =(a:symdef, b:symdef) boolean

Export symbol(modref, seq.word, mytype) symbol{From symbol}

Export symbol(modref, seq.word, seq.mytype, mytype) symbol{From symbol}

Export symIdxNB(seqparatype:mytype) symbol

Export type:addrsym

Export addr(addrsym) int

Export sym(addrsym) symbol

Export addrsym(int, symbol) addrsym

Export type:midpoint

Export libmods(m:midpoint) seq.modExports

Export option(midpoint) seq.word

Export prg(midpoint) set.symdef

Export src(midpoint) seq.seq.word

Export templates(midpoint) set.symdef

Export typedict(midpoint) typedict

Export type:modExports

Export exports(modExports) seq.symbol

Export modname(modExports) modref

Export types(modExports) seq.seq.mytype

Export modExports(modname:modref, exports:seq.symbol, types:seq.seq.mytype) modExports

Export type:modref{From mytype}

Export %(modref) seq.word{From mytype}

Export isAbstract(modref) boolean{From mytype}

Export library(modref) word{From mytype}

Export name(modref) word{From mytype}

Export para(modref) mytype{From mytype}

Export type:mytype{From mytype}

Export %(t:mytype) seq.word{From mytype}

Export parameter(mytype) mytype{From mytype}

Export seqof(mytype) mytype{From mytype}

Export moduleref(seq.word) modref{From mytype}

Export typeref(seq.word) mytype{From mytype}

Export type:typedef{From mytype}

Export =(modref, modref) boolean{From mytype}

Export =(mytype, mytype) boolean{From mytype}

Export >1(mytype, mytype) ordering{From mytype}

Export addabstract(mytype, mytype) mytype{From mytype}

Export internalmod modref{From mytype}

Export moduleref(seq.word, mytype) modref{From mytype}

Export typeT mytype{From mytype}

Export typeboolean mytype{From mytype}

Export typeint mytype{From mytype}

Export typeptr mytype{From mytype}

Export typereal mytype{From mytype}

Export %(seq.symbol) seq.word{From seq1.symbol}

Export Lit(int) symbol{From symbol}

Export Local(int) symbol{From symbol}

Export Reallit(i:int) symbol{From symbol}

Export continue(i:int) symbol{From symbol}

Export Start(mytype) symbol{From symbol}

Export builtinmod(mytype) modref{From symbol}

Export deepcopySym(mytype) symbol{From symbol}

Export isseq(mytype) boolean{From symbol}

Export Record(seq.mytype) symbol{From symbol}

Export Words(seq.word) symbol{From symbol}

Export type:symbol{From symbol}

Export %(symbol) seq.word{From symbol}

Export Fref(s:symbol) symbol{From symbol}

Export basesym(s:symbol) symbol{From symbol}

Export brf(symbol) int{From symbol}

Export brt(symbol) int{From symbol}

Export clearrequiresbit(symbol) symbol{From symbol}

Export firstvar(symbol) int{From symbol}

Export fullname(symbol) seq.word{From symbol}

Export hash(symbol) int{From symbol}

Function isOrdinary seq.symbolKind [kother, kcompoundname, kcat, kidx, kmakereal, kmember]

Function isInternal(sym:symbol) boolean name.module.sym = "internal" sub 1

Function isconstantorspecial(s:symbol) boolean between(kind.s, kfref, kendblock)

Export issimplename(symbol) boolean{From symbol}

Function isspecial(kind:symbolKind) boolean between(kind, klocal, kendblock)

Function isconst(s:symbol) boolean toint.kind.s ≤ toint.kconstantrecord

Export isunbound(symbol) boolean{From symbol}

Export module(symbol) modref{From symbol}

Export name(symbol) word{From symbol}

Export nametype(symbol) seq.mytype{From symbol}

Export nopara(symbol) int{From symbol}

Export paratypes(symbol) seq.mytype{From symbol}

Export privatefields(s:symbol) seq.int{From symbol}

Export resulttype(symbol) mytype{From symbol}

Export types(symbol) seq.mytype{From symbol}

Export value(symbol) int{From symbol}

Export worddata(symbol) seq.word{From symbol}

Export wordname(symbol) word{From symbol}

Export type:symdef{From symbol}

Export code(symdef) seq.symbol{From symbol}

Export externalNo(sd:symdef) int{From symbol}

Export ∈(a:symdefOption, b:symdefOption) boolean

Export options(sd:symdef) symdefOption{From symbol}

Export isThisLibrary(sd:symdef) boolean{From symbol}

Export paragraphno(symdef) int{From symbol}

Export sym(symdef) symbol{From symbol}

Export symdef(symbol, seq.symbol, int) symdef{From symbol}

Export Word(word) symbol{From symbol}

Export =(symbol, symbol) boolean{From symbol}

Export >1(a:symdef, b:symdef) ordering{From symbol}

Export >1(symbol, symbol) ordering{From symbol}

Export >2(symbol, symbol) ordering{From symbol}

Export Br2(int, int) symbol{From symbol}

Export Define(word, int) symbol{From symbol}

Export EndBlock symbol{From symbol}

Export Exit symbol{From symbol}

Export GetSeqLength symbol{From symbol}

Export GetSeqType symbol{From symbol}

Export Litfalse symbol{From symbol}

Export Littrue symbol{From symbol}

Export Local(name:word, type:mytype, parano:int) symbol{From symbol}

Export Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype) symbol{From symbol}

Export NotOp symbol{From symbol}

Export PlusOp symbol{From symbol}

Export PreFref symbol{From symbol}

Export Sequence(mytype, int) symbol{From symbol}

Export getCode(set.symdef, symbol) seq.symbol{From symbol}

Export getSymdef(set.symdef, symbol) set.symdef{From symbol}

Export replaceTsymbol(mytype, symbol) symbol{From symbol}

Function istype(s:symbol) boolean
not.issimplename.s ∧ wordname.s = "type" sub 1 ∧ nopara.s = 1

Export kind(s:symbol) symbolKind

Export symbol4(modref, word, mytype, seq.mytype, mytype) symbol{From symbol}

Export symdef4(
sym:symbol
, code:seq.symbol
, paragraphno:int
, options:symdefOption
) symdef
{From symbol}

Export type:symdefOption

Export NOOPTIONS symdefOption

Export ThisLibrary symdefOption

Export PROFILE symdefOption

Export STATE symdefOption

Export COMPILETIME symdefOption

Export NOINLINE symdefOption

Export INLINE symdefOption

Export VERYSIMPLE symdefOption

Export COMMAND symdefOption

Export nonReducible symdefOption

Export %(a:symdefOption) seq.word

Export +(a:symdefOption, b:symdefOption) symdefOption

Export ∩(a:symdefOption, b:symdefOption) symdefOption

Export \(a:symdefOption, b:symdefOption) symdefOption

Export =(a:symdefOption, b:symdefOption) boolean

Export type? mytype{From symbol}

Export typebits mytype{From symbol}

Export typebyte mytype{From symbol}

Export typeword mytype{From symbol}

Export fullconstantcode(s:symbol) seq.symbol{From symbolconstant}

Export type:symbolconstant{From symbolconstant}

Export Constant2(libname:word, args:seq.symbol) symbol{From symbolconstant}

Export type:typedict{From typedict}

Export type:typeentry{From typedict}

Export basetype(mytype, typedict) mytype{From typedict}

Export basetype(seq.mytype, typedict) seq.mytype{From typedict}

Export emptytypedict typedict{From typedict}

Function midpoint5(
a:seq.word
, b:set.symdef
, c:set.symdef
, d:typedict
, e:seq.modExports
, f:seq.seq.word
) midpoint
midpoint(a, b, c, d, e, f)

type addrsym is addr:int, sym:symbol

type modExports is modname:modref, exports:seq.symbol, types:seq.seq.mytype

Function empty:midpoint midpoint
midpoint(
 ""
 , empty:set.symdef
 , empty:set.symdef
 , emptytypedict
 , empty:seq.modExports
 , empty:seq.seq.word
)

Function midpoint(
option:seq.word
, prg:set.symdef
, typedict:typedict
, libmods:seq.modExports
, src:seq.seq.word
) midpoint
midpoint(option, prg, empty:set.symdef, typedict, libmods, src)

type midpoint is
option:seq.word
, prg:set.symdef
, templates:set.symdef
, typedict:typedict
, libmods:seq.modExports
, src:seq.seq.word

Function libname(info:midpoint) word
let a = extractValue(option.info, "Library"),
(if isempty.a then "noName" else a) sub 1

Export typebase(i:int) mytype{From mytype}

Export type:modref{From mytype}

Export %(modref) seq.word{From mytype}

Export isAbstract(modref) boolean{From mytype}

Export isSimple(modref) boolean{From mytype}

Export library(modref) word{From mytype}

Export name(modref) word{From mytype}

Export para(modref) mytype{From mytype}

Export type:mytype{From mytype}

Export %(p:mytype) seq.word{From mytype}

Export abstractModref(mytype) modref{From mytype}

Export abstracttype(mytype) mytype{From mytype}

Export abstracttypename(mytype) word{From mytype}

Export isAbstract(m:mytype) boolean{From mytype}

Export parameter(mytype) mytype{From mytype}

Export processof(mytype) mytype{From mytype}

Export seqof(mytype) mytype{From mytype}

Export tomodref(mytype) modref{From mytype}

Export type:passtypes{From mytype}

Export moduleref(seq.word) modref{From mytype}

Export typeref(seq.word) mytype{From mytype}

Export >1(modref, modref) ordering{From mytype}

Export >1(typedef, typedef) ordering{From mytype}

Export addabstract(a:mytype, t:mytype) mytype{From mytype}

Export internalmod modref{From mytype}

Export moduleref(seq.word, para:mytype) modref{From mytype}

Export replaceT(mytype, modref) modref{From mytype}

Export replaceT(with:mytype, m:mytype) mytype{From mytype}

Export typeT mytype{From mytype}

Export typeboolean mytype{From mytype}

Export typeint mytype{From mytype}

Export typeptr mytype{From mytype}

Export typereal mytype{From mytype}

Export type:set.symbol{From set.symbol}

Export changelibrary(symbol, seq.word) symbol

Export Define(int) symbol

Export typepacked2 mytype

Export typepacked3 mytype

Export typepacked4 mytype

Export typepacked5 mytype

Export typepacked6 mytype

Export replacestar(symbol, word) symbol

Export ifthenelse(seq.symbol, seq.symbol, seq.symbol, mytype) seq.symbol

Export EqOp symbol

Export Label(int) symbol

Export Lit(word) symbol

Export deepcopyseqword symbol

Export Jmp(seq.symbol) seq.symbol

Export iscore4(mytype) boolean

Export hasrequires(symbol) boolean

Export setunbound(symbol) symbol

Export setrequires(symbol) symbol

Export GtOp symbol

Export isconst(s:symbolKind) boolean

Function -(a:symbolKind, b:symbolKind) int toint.a - toint.b

Export isencoding(mytype) boolean

Export Getfld(mytype) symbol

Export setSym(mytype) symbol

Export outofboundssymbol symbol

Export between(symbolKind, symbolKind, symbolKind) boolean

Export %(symbolKind) seq.word

Export ∈(symbolKind, seq.symbolKind) boolean

use seq.symbolKind

Export =(a:symbolKind, b:symbolKind) boolean

Export type:symbolKind

Export kfref symbolKind

Export kwords symbolKind

Export kword symbolKind

Export kint symbolKind

Export kreal symbolKind

Export kfalse symbolKind

Export ktrue symbolKind

Export kconstantrecord symbolKind

Export klocal symbolKind

Export kdefine symbolKind

Export ksequence symbolKind

Export krecord symbolKind

Export kloop symbolKind

Export kstart symbolKind

Export kbr symbolKind

Export kjmpB symbolKind

Export klabel symbolKind

Export kjmp symbolKind

Export kcontinue symbolKind

Export kexit symbolKind

Export kendblock symbolKind

Export kother symbolKind

Export kidxNB symbolKind

Export kidx symbolKind

Export kcompoundname symbolKind

Export kmember symbolKind

Export kcat symbolKind

Export kstacktrace symbolKind

Export knot symbolKind

Export kgetseqlength symbolKind

Export kgetseqtype symbolKind

Export keqlI symbolKind

Export keqlB symbolKind

Export keqlreal symbolKind

Export kintpart symbolKind

Export kcasttoreal symbolKind

Export ktoreal symbolKind

Export ktointbyte symbolKind

Export ktointbit symbolKind

Export krepresentation symbolKind

Export kmulreal symbolKind

Export kdivreal symbolKind

Export kaddreal symbolKind

Export ksubreal symbolKind

Export k>1real symbolKind

Export kmulint symbolKind

Export kdivint symbolKind

Export kaddint symbolKind

Export ksubint symbolKind

Export k>1int symbolKind

Export kgrtI symbolKind

Export k<<bits symbolKind

Export k>>bits symbolKind

Export kxorbits symbolKind

Export k∨bits symbolKind

Export k∧bits symbolKind

Export kabortR symbolKind

Export kabortI symbolKind

Export kabortB symbolKind

Export kabortP symbolKind

Export ksetI symbolKind

Export ksetR symbolKind

Export ksetP symbolKind

Export kprefref symbolKind

Export kbuiltin symbolKind

Export kglobal symbolKind

Export kmakereal symbolKind

Export kfld symbolKind

Export kcreatethreadZ symbolKind

Export kinternalmod symbolKind

Export kbuiltincompound symbolKind 