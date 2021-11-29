Module symbol2

use symbolconstant

use compilerfront

use mytype

use pass2

use standard

use symbol

use typedict

use seq.mytype

use set.symdef

Export basesym(s:symbol)symbol

Export library(modref)word

Export symdef(symbol, seq.symbol, int)symdef

Export type:symbolconstant

Export Constant2(seq.symbol) symbol

Export constantcode(s:symbol)seq.symbol

Export type:symbol

Export value(symbol)int

Export nopara(symbol)int

Export paratypes(symbol)seq.mytype

Export name(symbol)word

Export nametype(sym:symbol)seq.mytype

Export internalmod modref

Export typeboolean mytype

Export symbol(modref, seq.word, mytype, mytype, mytype)symbol

Export Lit(int)symbol

Export isstart(symbol)boolean

Export isexit(symbol)boolean

Export isbr(symbol)boolean

Export module(symbol)modref

Export name(modref)word

Export isdefine(symbol)boolean

Export iswords(symbol)boolean

Export worddata(symbol)seq.word

Export isblock(symbol)boolean

Export isconst(symbol)boolean

Export isRealLit(symbol)boolean

Export isIntLit(symbol)boolean

Export isFref(symbol)boolean

Export isRecord(symbol)boolean

Export isloopblock(symbol)boolean

Export iscontinue(symbol)boolean

Export islocal(symbol)boolean

Export types(symbol)seq.mytype

Export firstvar(symbol)int

Export isword(symbol)boolean

Export isspecial(symbol)boolean

Export fullname(symbol)seq.word

Export isSequence(symbol)boolean

Export isBuiltin(symbol)boolean

Export isunbound(symbol)boolean

Export Litfalse symbol

Export Littrue symbol

Export PlusOp symbol

Export Br2(int, int)symbol

Export typebits mytype

Export symbol(modref, seq.word, mytype, mytype)symbol

Export symbol(modref, seq.word, seq.mytype, mytype)symbol

Export symbol(modref, seq.word, mytype, mytype, mytype, mytype)symbol

Export symbol(modref, seq.word, mytype)symbol

Export typeword mytype

Export type? mytype

Export typebyte mytype

Export typebit mytype

Export builtinmod(mytype)modref

Export abortsymbol(mytype)symbol

Export Start(mytype)symbol

Export Exit symbol

Export EndBlock symbol

Export type:mytype

Export parameter(mytype)mytype

Export NotOp symbol

Export GetSeqType symbol

Export GetSeqLength symbol

Export=(symbol, symbol)boolean

Export ?(symbol, symbol)ordering

Export type:symdef

Export sym(symdef)symbol

Export code(symdef)seq.symbol

Export print(symbol)seq.word

Export print(seq.symbol)seq.word

Export removeoptions(seq.symbol)seq.symbol

Export resulttype(symbol)mytype

Export=(modref, modref)boolean

Export typeint mytype

Export typeptr mytype

Export typereal mytype

Export=(mytype, mytype)boolean

Export isseq(mytype)boolean

Export print(mytype)seq.word

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

Export coretype(mytype, typedict)mytype

Export ?(symdef, symdef)ordering

Export type:modref

Export para(modref)mytype

Export name(modref)word

Export moduleref(seq.word)modref

Export wordname(symbol)word

Export symbol4(modref, word, mytype, seq.mytype, mytype)symbol

Export typeT mytype

Export addabstract(mytype, mytype)mytype

Export moduleref(seq.word, mytype)modref

Export isrecordconstant(symbol)boolean

Export iswordseq(symbol)boolean

Export brt(symbol)int

Export brf(symbol)int

Export isstartorloop(symbol)boolean

Export fsighash(symbol)int

Export Sequence(mytype, int)symbol

Export hash(symbol)int

Export Record(seq.mytype)symbol

Export getCode(set.symdef, symbol)seq.symbol

Export basetype(mytype, typedict)mytype

Export type:typedef 