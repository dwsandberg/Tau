Module symbol2

use seq.modExports

use mytype

use standard

use symbol

use otherseq.symbol

use symbolconstant

use set.symdef

use typedict

Export type:midpoint

Export libmods(m:midpoint) seq.modExports

Export option(midpoint) seq.word

Export prg(midpoint) set.symdef

Export src(midpoint) seq.seq.word

Export templates(midpoint) set.symdef

Export typedict(midpoint) typedict

Export midpoint(seq.word, set.symdef, set.symdef, typedict, seq.modExports, seq.seq.word) midpoint

Export type:modExports

Export exports(modExports) seq.symbol

Export modname(modExports) modref

Export types(modExports) seq.seq.mytype

Export modExports(modname:modref, exports:seq.symbol, types:seq.seq.mytype) modExports

Export type:modref {From mytype}

Export isabstract(modref) boolean {From mytype}

Export library(modref) word {From mytype}

Export name(modref) word {From mytype}

Export para(modref) mytype {From mytype}

Export type:mytype {From mytype}

Export %(t:mytype) seq.word {From mytype}

Export parameter(mytype) mytype {From mytype}

Export seqof(mytype) mytype {From mytype}

Export moduleref(seq.word) modref {From mytype}

Export typeref(seq.word) mytype {From mytype}

Export type:typedef {From mytype}

Export =(modref, modref) boolean {From mytype}

Export =(mytype, mytype) boolean {From mytype}

Export >1(mytype, mytype) ordering {From mytype}

Export addabstract(mytype, mytype) mytype {From mytype}

Export internalmod modref {From mytype}

Export moduleref(seq.word, mytype) modref {From mytype}

Export typeT mytype {From mytype}

Export typeboolean mytype {From mytype}

Export typeint mytype {From mytype}

Export typeptr mytype {From mytype}

Export typereal mytype {From mytype}

Export %(seq.symbol) seq.word {From otherseq.symbol}

Export Lit(int) symbol {From symbol}

Export Local(int) symbol {From symbol}

Export Reallit(i:int) symbol {From symbol}

Export continue(i:int) symbol {From symbol}

Export Start(mytype) symbol {From symbol}

Export abortsymbol(mytype) symbol {From symbol}

Export builtinmod(mytype) modref {From symbol}

Export deepcopySym(mytype) symbol {From symbol}

Export isseq(mytype) boolean {From symbol}

Export Record(seq.mytype) symbol {From symbol}

Export getoption(seq.symbol) seq.word {From symbol}

Export removeoptions(seq.symbol) seq.symbol {From symbol}

Export Words(seq.word) symbol {From symbol}

Export type:symbol {From symbol}

Export %(symbol) seq.word {From symbol}

Export Fref(s:symbol) symbol {From symbol}

Export basesym(s:symbol) symbol {From symbol}

Export brf(symbol) int {From symbol}

Export brt(symbol) int {From symbol}

Export clearrequiresbit(symbol) symbol {From symbol}

Export firstvar(symbol) int {From symbol}

Export fullname(symbol) seq.word {From symbol}

Export hash(symbol) int {From symbol}

Export inModFor(sym:symbol) boolean {From symbol}

Export isBuiltin(symbol) boolean {From symbol}

Export isFref(symbol) boolean {From symbol}

Export isGlobal(symbol) boolean {From symbol}

Export isIntLit(symbol) boolean {From symbol}

Export isInternal(sym:symbol) boolean {From symbol}

Export isRealLit(symbol) boolean {From symbol}

Export isRecord(symbol) boolean {From symbol}

Export isSequence(symbol) boolean {From symbol}

Export isblock(symbol) boolean {From symbol}

Export isbr(symbol) boolean {From symbol}

Export isconst(symbol) boolean {From symbol}

Export isconstantorspecial(symbol) boolean {From symbol}

Export iscontinue(symbol) boolean {From symbol}

Export isdefine(symbol) boolean {From symbol}

Export isexit(symbol) boolean {From symbol}

Export islocal(symbol) boolean {From symbol}

Export isloopblock(symbol) boolean {From symbol}

Export isrecordconstant(symbol) boolean {From symbol}

Export issimplename(symbol) boolean {From symbol}

Export isspecial(symbol) boolean {From symbol}

Export isstart(symbol) boolean {From symbol}

Export isstartorloop(symbol) boolean {From symbol}

Export isunbound(symbol) boolean {From symbol}

Export isword(symbol) boolean {From symbol}

Export iswords(symbol) boolean {From symbol}

Export iswordseq(symbol) boolean {From symbol}

Export module(symbol) modref {From symbol}

Export name(symbol) word {From symbol}

Export nametype(symbol) seq.mytype {From symbol}

Export nopara(symbol) int {From symbol}

Export paratypes(symbol) seq.mytype {From symbol}

Export privatefields(s:symbol) seq.int {From symbol}

Export resulttype(symbol) mytype {From symbol}

Export types(symbol) seq.mytype {From symbol}

Export value(symbol) int {From symbol}

Export worddata(symbol) seq.word {From symbol}

Export wordname(symbol) word {From symbol}

Export symbol(modref, seq.word, mytype) symbol {From symbol}

Export symbol(modref, seq.word, mytype, mytype) symbol {From symbol}

Export symbol(modref, seq.word, mytype, mytype, mytype) symbol {From symbol}

Export symbol(modref, seq.word, mytype, mytype, mytype, mytype) symbol {From symbol}

Export symbol(modref, seq.word, seq.mytype, mytype) symbol {From symbol}

Export type:symdef {From symbol}

Export code(symdef) seq.symbol {From symbol}

Export paragraphno(symdef) int {From symbol}

Export sym(symdef) symbol {From symbol}

Export symdef(symbol, seq.symbol, int) symdef {From symbol}

Export Word(word) symbol {From symbol}

Export =(symbol, symbol) boolean {From symbol}

Export >1(a:symdef, b:symdef) ordering {From symbol}

Export >1(symbol, symbol) ordering {From symbol}

Export Br2(int, int) symbol {From symbol}

Export Define(word, int) symbol {From symbol}

Export EndBlock symbol {From symbol}

Export Exit symbol {From symbol}

Export GetSeqLength symbol {From symbol}

Export GetSeqType symbol {From symbol}

Export Litfalse symbol {From symbol}

Export Littrue symbol {From symbol}

Export Local(name:word, type:mytype, parano:int) symbol {From symbol}

Export Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype) symbol
{From symbol}

Export NotOp symbol {From symbol}

Export Optionsym symbol {From symbol}

Export PlusOp symbol {From symbol}

Export PreFref symbol {From symbol}

Export Sequence(mytype, int) symbol {From symbol}

Export addoption(seq.symbol, seq.word) seq.symbol {From symbol}

Export getCode(set.symdef, symbol) seq.symbol {From symbol}

Export getSymdef(set.symdef, symbol) set.symdef {From symbol}

Export symbol4(modref, word, mytype, seq.mytype, mytype) symbol {From symbol}

Export symconst(i:int, hashfref:boolean) symbol {From symbol}

Export type? mytype {From symbol}

Export typebits mytype {From symbol}

Export typebyte mytype {From symbol}

Export typeword mytype {From symbol}

Export Constant2(args:seq.symbol) symbol {From symbolconstant}

Export renumberconstants(prg:seq.symdef) seq.symdef {From symbolconstant}

Export fullconstantcode(s:symbol) seq.symbol {From symbolconstant}

Export type:symbolconstant {From symbolconstant}

Export type:typedict {From typedict}

Export type:typeentry {From typedict}

Export basetype(mytype, typedict) mytype {From typedict}

Export emptytypedict typedict {From typedict}

type modExports is modname:modref, exports:seq.symbol, types:seq.seq.mytype

Function empty:midpoint midpoint
midpoint(""
 , empty:set.symdef
 , empty:set.symdef
 , emptytypedict
 , empty:seq.modExports
 , empty:seq.seq.word)

Function midpoint(option:seq.word, prg:set.symdef, typedict:typedict, libmods:seq.modExports, src:seq.seq.word) midpoint
midpoint(option, prg, empty:set.symdef, typedict, libmods, src)

type midpoint is option:seq.word
 , prg:set.symdef
 , templates:set.symdef
 , typedict:typedict
 , libmods:seq.modExports
 , src:seq.seq.word 