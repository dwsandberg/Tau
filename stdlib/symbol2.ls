Module symbol2

use seq.modExports

use mytype

use standard

use symbol

use symbolconstant

use set.symdef

use typedict

Export clearrequiresbit(symbol)symbol

Export privatefields(s:symbol)seq.int

Export Local(int)symbol

Export getSymdef(set.symdef, symbol)set.symdef

Export deepcopySym(mytype)symbol

Export renumberconstants(prg:seq.symdef)seq.symdef

Export fullconstantcode(s:symbol)seq.symbol

Export Constant2(args:seq.symbol)symbol

Export type:symbolconstant

Export paragraphno(symdef)int

Export basesym(s:symbol)symbol

Export library(modref)word

Export symdef(symbol, seq.symbol, int)symdef

Export type:symbol

Export internalmod modref

Export name(modref)word

Export typeboolean mytype

Export value(symbol)int

Export nopara(symbol)int

Export paratypes(symbol)seq.mytype

Export name(symbol)word

Export nametype(symbol)seq.mytype

Export module(symbol)modref

Export resulttype(symbol)mytype

Export wordname(symbol)word

Export worddata(symbol)seq.word

Export fullname(symbol)seq.word

Export types(symbol)seq.mytype

Export firstvar(symbol)int

Export brt(symbol)int

Export brf(symbol)int

Export hash(symbol)int

Export inModFor(sym:symbol)boolean

Export isstart(symbol)boolean

Export isexit(symbol)boolean

Export isbr(symbol)boolean

Export isdefine(symbol)boolean

Export iswords(symbol)boolean

Export isblock(symbol)boolean

Export isconst(symbol)boolean

Export isconstantorspecial(symbol)boolean

Export isGlobal(symbol)boolean

Export isRealLit(symbol)boolean

Export isIntLit(symbol)boolean

Export isInternal(sym:symbol)boolean

Export isFref(symbol)boolean

Export isRecord(symbol)boolean

Export isloopblock(symbol)boolean

Export iscontinue(symbol)boolean

Export islocal(symbol)boolean

Export isword(symbol)boolean

Export isspecial(symbol)boolean

Export isSequence(symbol)boolean

Export isBuiltin(symbol)boolean

Export isunbound(symbol)boolean

Export isrecordconstant(symbol)boolean

Export iswordseq(symbol)boolean

Export isstartorloop(symbol)boolean

Export issimplename(symbol)boolean

Export typebits mytype

Export typeword mytype

Export type? mytype

Export typebyte mytype

Export builtinmod(mytype)modref

Export type:mytype

Export parameter(mytype)mytype

Export abortsymbol(mytype)symbol

Export Br2(int, int)symbol

Export continue(i:int)symbol

Export Define(word, int)symbol

Export EndBlock symbol

Export Exit symbol

Export Fref(s:symbol)symbol

Export GetSeqType symbol

Export GetSeqLength symbol

Export Lit(int)symbol

Export Litfalse symbol

Export Littrue symbol

Export Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype)symbol

Export Local(name:word, type:mytype, parano:int)symbol

Export NotOp symbol

Export Optionsym symbol

Export PlusOp symbol

Export PreFref symbol

Export Reallit(i:int)symbol

Export Record(seq.mytype)symbol

Export Sequence(mytype, int)symbol

Export Start(mytype)symbol

Export symbol(modref, seq.word, mytype, mytype, mytype)symbol

Export symbol(modref, seq.word, mytype, mytype)symbol

Export symbol(modref, seq.word, seq.mytype, mytype)symbol

Export symbol(modref, seq.word, mytype, mytype, mytype, mytype)symbol

Export symbol(modref, seq.word, mytype)symbol

Export symbol4(modref, word, mytype, seq.mytype, mytype)symbol

Export symconst(i:int, hashfref:boolean)symbol

Export Word(word)symbol

Export Words(seq.word)symbol

Export=(symbol, symbol)boolean

Export ?(symbol, symbol)ordering

Export type:symdef

Export sym(symdef)symbol

Export code(symdef)seq.symbol

Export print(symbol)seq.word

Export print(seq.symbol)seq.word

Export removeoptions(seq.symbol)seq.symbol

Export addoption(seq.symbol, seq.word)seq.symbol

Export getoption(seq.symbol)seq.word

Export=(modref, modref)boolean

Export typeint mytype

Export typeptr mytype

Export typereal mytype

Export=(mytype, mytype)boolean

Export isseq(mytype)boolean

Export print(mytype)seq.word

Function %(t:mytype)seq.word print.t

Export isabstract(modref)boolean

Export ?(mytype, mytype)ordering

Export typeref(seq.word)mytype

Export seqof(mytype)mytype

Export type:typedict

Export type:typeentry

Export ?(a:symdef, b:symdef)ordering

Export ?(symdef, symdef)ordering

Export type:modref

Export para(modref)mytype

Export name(modref)word

Export moduleref(seq.word)modref

Export typeT mytype

Export addabstract(mytype, mytype)mytype

Export moduleref(seq.word, mytype)modref

Export getCode(set.symdef, symbol)seq.symbol

Export basetype(mytype, typedict)mytype

Export type:typedef

type modExports is modname:modref, exports:seq.symbol, types:seq.seq.mytype

Export exports(modExports)seq.symbol

Export modname(modExports)modref

Export types(modExports)seq.seq.mytype

Export modExports(modname:modref, exports:seq.symbol, types:seq.seq.mytype)modExports

Export type:modExports

Export emptytypedict typedict

Function empty:midpoint midpoint
midpoint(""
, empty:set.symdef
, empty:set.symdef
, emptytypedict
, empty:seq.modExports
, empty:seq.seq.word
)

Function midpoint(option:seq.word, prg:set.symdef, typedict:typedict, libmods:seq.modExports, src:seq.seq.word)midpoint
midpoint(option, prg, empty:set.symdef, typedict, libmods, src)

type midpoint is option:seq.word
, prg:set.symdef
, templates:set.symdef
, typedict:typedict
, libmods:seq.modExports
, src:seq.seq.word


Export midpoint(seq.word, set.symdef, set.symdef, typedict, seq.modExports, seq.seq.word)midpoint

Export prg(midpoint)set.symdef

Export option(midpoint)seq.word

Export templates(midpoint)set.symdef

Export typedict(midpoint)typedict

Export type:midpoint

Export src(midpoint)seq.seq.word

Export libmods(m:midpoint)seq.modExports 