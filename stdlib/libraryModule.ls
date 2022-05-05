Module libraryModule

use bits

use standard

use symbol2

use seq.bits

use seq.char

use seq.libraryModule

use encoding.symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use seq.symbolref

use seq.seq.mytype

use otherseq.seq.symbol

use set.seq.symbol

use otherseq.seq.symbolref

use seq.seq.symbolref

use seq.seq.word

use seq.encodingpair.seq.char

Export type:symbolref

Export symbolref(sym:symbol)symbolref symbolref.addorder.sym

Export decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s)

type libraryModule is modname:modref, exports:seq.symbolref, types:seq.seq.mytype

Export libraryModule(modname:modref, exports:seq.symbolref, types:seq.seq.mytype)libraryModule

Export type:libraryModule

Export exports(libraryModule)seq.symbolref

Export modname(libraryModule)modref

Export types(libraryModule)seq.seq.mytype

Function convert(s:seq.modExports) seq.libraryModule
 for all=empty:seq.libraryModule, m /in s do
   for acc=empty:seq.symbolref,   sym /in exports.m do acc+symbolref.sym  
/for(all+libraryModule(modname.m,acc,types.m))
/for(all)


______________________

type parc is caller:symbolref, callee:symbolref, counts:int, clocks:int, space:int, unused:int

Export type:parc

Export parc(caller:symbolref, callee:symbolref, counts:int, clocks:int, space:int, unused:int)parc

Function =(a:parc, b:parc)boolean toint.callee.a = toint.callee.b ∧ toint.caller.a = toint.caller.b

Export caller(parc)symbolref

Export callee(parc)symbolref

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

Export type:liblib

___________________________

type liblib is libname:seq.word
, words:seq.encodingpair.seq.char
, entrypointaddress:int
, timestamp:int
, profiledata:seq.parc
, libinfo:compileinfo
, symboladdress:seq.int


Export symboladdress(liblib)seq.int

Export entrypointaddress(liblib)int

Export libinfo(liblib)compileinfo

Function code(l:liblib)seq.seq.symbolref code.libinfo.l

Export timestamp(liblib)int

Function decoderef(l:liblib)seq.symbol symbolrefdecode.libinfo.l

Export libname(liblib)seq.word

Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

_________________

type compileinfo is symbolrefdecode:seq.symbol
, mods:seq.libraryModule
, code:seq.seq.symbolref
, src:seq.seq.word
, typedict:typedict

Export compileinfo(symbolrefdecode:seq.symbol
, mods:seq.libraryModule
, code:seq.seq.symbolref
, src:seq.seq.word
, typedict:typedict) compileinfo

use otherseq.symbolref

Function  changestacktrace(info:compileinfo) compileinfo
  let traceimpsym=symbol(moduleref."inputoutput","stacktraceimp",seqof.typeword)
  let tracesym=symbol(internalmod,"stacktrace",seqof.typeword)
   let impidx=symbolref.findindex(traceimpsym,symbolrefdecode.info )
    let traceidx=symbolref.findindex(tracesym,symbolrefdecode.info) 
   if toint.traceidx > length.symbolrefdecode.info then 
   info else 
    assert toint.impidx /le length.symbolrefdecode.info report "cannot find
     stacktraceimp"
   for  acc=empty:seq.seq.symbolref , def /in code.info do
     let b=break(traceidx,def << 2) 
     acc+if length.b=1 then def
     else for acc1=subseq(def,1,2),p /in b do acc1+p+impidx /for(acc1 >> 1) 
  /for(
  compileinfo( symbolrefdecode.info
, mods.info
, acc
, src.info
, typedict.info))
   

Function libname(info:compileinfo)word extractValue(first.src.info, "Library")_1



Export type:compileinfo

Export code(compileinfo)seq.seq.symbolref

Function modsM(c:compileinfo)seq.libraryModule  mods.c

Export typedict(compileinfo)typedict

Export symbolrefdecode(compileinfo)seq.symbol

Export src(compileinfo)seq.seq.word

use seq.modExports

Function modsE(ci:compileinfo) seq.modExports 
 for mods=empty:seq.modExports ,m /in mods.ci do  
    mods+modExports(modname.m ,for acc=empty:seq.symbol, r /in exports.m  do acc+ci_r /for(acc),  types.m)
 /for(mods)


Function profiledata(info:compileinfo)seq.int
let l = first.code.info << 4
for acc = [1, length.l / 2], first = true, r ∈ l do
 if first then next(acc + toint.r, false)else next(acc + toint.r + [0, 0, 0, 0], true)
/for(acc)


Function newmaplength(info:compileinfo)int toint.(first.code.info)_2

Function libcodelength(info:compileinfo)int toint.(first.code.info)_3

Function addresslength(info:compileinfo)int toint.(first.code.info)_4

Function libcode(info:compileinfo)seq.seq.symbolref subseq(code.info, 2, libcodelength.info + 1)

Function prgcode(info:compileinfo)seq.seq.symbolref subseq(code.info, libcodelength.info + 2, length.code.info)

Function _(info:compileinfo, r:symbolref)symbol
let i = toint.r
if i > 0 then(symbolrefdecode.info)_i else Fref.(symbolrefdecode.info)_(-i)

Function roots(s:compileinfo)set.symbol
let exports = 
 for exports = empty:seq.symbolref, m ∈ mods.s do exports + exports.m /for(exports)
for acc = empty:set.symbol, r ∈ exports do acc + s_r /for(acc)


use seq.symdef

Function prg(s:compileinfo)seq.symdef
for acc4 = empty:seq.symdef, c ∈ code.s do
 let sym = s_(c_1)
  let paragraphno=if length.c =1 /or not.isconst.s_(c_2)   then 0 else   value.s_(c_2)
 acc4 + symdef(sym, for acc = empty:seq.symbol, r ∈ c << 2 do acc + s_r /for(acc),paragraphno)
/for(acc4)


use set.symdef

use seq.symbolref

use seq.mytype

use set.modref

use set.symbol

use set.mytype


use seq.seq.mytype


Function tomidpoint(org:midpoint, libinfo:compileinfo, libname:word)midpoint
let orgprg = prg.org
let prg0 = 
 for acc = orgprg, c ∈ code.libinfo do
  if toint.first.c = 0 then acc
  else
   for code = empty:seq.symbol, r ∈ c << 1 do code + libinfo_r /for(symdef(libinfo_(c_1), code,0) ∪ acc)
 /for(acc)
let prg = 
 for acc = prg0, idx = 1, sym ∈ symbolrefdecode.libinfo do
  if isconstantorspecial.sym ∨ isabstract.module.sym ∨ library.module.sym ≠ libname then next(acc, idx + 1)
  else next(symdef(sym, addoption(getCode(acc, sym), "COMPILED"),idx+1) ∪ acc, idx + 1)
 /for(toseq.acc)
midpoint( "",asset.prg,emptytypedict, libmods.org+modsE.libinfo ,empty:seq.seq.word)



Function symbolrefdecode seq.symbol
for acc = empty:seq.symbol, p ∈ encodingdata:symbol do acc + p /for(acc) 