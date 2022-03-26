Module compilerfrontT.T

use compilerfront

use standard

use symbol

use typedict

use process.compileinfo

use set.symdef

use seq.seq.word

unbound dependentinfo:T(s:seq.word)loadedresult

unbound pass2:T(set.symdef, typedict, option:seq.word)set.symdef

Function compileinfo:T(option:seq.word, info:seq.seq.word)process.compileinfo
{OPTION INLINE}
let dependentlibs = dependentinfo:T(extractValue(info,"uses"))
YYYY:T(option, info, dependentlibs)


Function compilerfront4:T(option:seq.word, allsrc:seq.seq.word, libinfo:loadedresult)compileinfo
let m = compilerfront3(option, allsrc, libinfo)
if first.option.m ∈ "library text hhh pass1"then
 compileinfo(toseq.prg.m, typedict.m, libmods.m, src.m)
else if option.m = "all"then
 let prg5 = pass2:T(prg.m, typedict.m, "") ∪ templates.m
 compilerback2(prg5, libmods.m, typedict.m, [first.src.m])
else
 {additionalpass:T(toseq.core+toseq.small+big, core, typedict)let prg4=for acc=prg.m, s /in toseq.prg.m do if js 
/in code.s /and"INLINE"_1 /in getoption.code.s then txt+" /br"+print.sym.s else txt /for(txt)}
 let prg5 = pass2:T(prg.m, typedict.m, "") ∪ templates.m
 let js = symbol(internalmod, "jsHTTP", constantseq(8, typereal), typereal)
 {let prg6=for acc=prg5, s /in toseq.prg5 do if js /in code.s /and"INLINE"_1 /nin getoption.code.s then addoption(acc 
, sym.s, "INLINE")else acc /for(pass2:T(acc, typedict.m, "addpass"))}
 compileinfo(toseq.prg5, typedict.m, libmods.m, src.m)

use libdesc

use otherseq.mytype

use seq.symbol

function YYYY:T(option:seq.word, info:seq.seq.word, dependentlibs:loadedresult)process.compileinfo
{OPTION NOINLINE}
{need because wasm interpreted code does not handle createthreadY}
process.compilerfront4:T(option, info, dependentlibs) 