Module symbol2

use compilerfront

use libraryModule

use mytype

use standard

use symbol

use typedict

use seq.mytype

use seq.symbol

use set.symdef

Function rehash(c:compileinfo)compileinfo
compileinfo(typedict.c
, code.c
, src.c
, for acc = empty:seq.symbol, sym ∈ symbolrefdecode.c do acc + rehash.sym /for(acc)
, mods.c
)

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

Export isstart(symbol)boolean

Export isexit(symbol)boolean

Export isbr(symbol)boolean

Export isdefine(symbol)boolean

Export iswords(symbol)boolean

Export isblock(symbol)boolean

Export isconst(symbol)boolean

Export isRealLit(symbol)boolean

Export isIntLit(symbol)boolean

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

Export typebit mytype

Export builtinmod(mytype)modref

Export type:mytype

Export parameter(mytype)mytype

Export abortsymbol(mytype)symbol

Export Br2(int, int)symbol

Export continue(i:int)symbol

Export Define(name:word, i:int) symbol

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

Export PlusOp symbol

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

Export symconst(i:int)symbol

Export Word(word) symbol

Export Words(seq.word) symbol

Export=(symbol, symbol)boolean

Export ?(symbol, symbol)ordering

Export type:symdef

Export sym(symdef)symbol

Export code(symdef)seq.symbol

Export print(symbol)seq.word

Export print(seq.symbol)seq.word

Export removeoptions(seq.symbol)seq.symbol

Export=(modref, modref)boolean

Export typeint mytype

Export typeptr mytype

Export typereal mytype

Export=(mytype, mytype)boolean

Export isseq(mytype)boolean

Export print(mytype)seq.word

Function %(t:mytype) seq.word print.t

Export isabstract(modref)boolean

Export ?(mytype, mytype)ordering

Export typeref(seq.word)mytype

Export seqof(mytype)mytype

Export symbolrefdecode(compileinfo)seq.symbol

Export toint(symbolref)int

Export type:symbolref

Export type:typedict

Export type:typeentry

Export prg(compileinfo)seq.symdef

Export type:compileinfo

Export typedict(compileinfo)typedict

Export roots(compileinfo)set.symbol

Export code(compileinfo)seq.seq.symbolref

Export src(compileinfo)seq.seq.word

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