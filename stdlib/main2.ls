Module main2

use UTF8

use bits

use seq.byte

use codegennew

use compilerfront

use debuginfo

use file

use seq.file

use process.seq.file

use format

use compilerfrontT.libllvm

use objectio.midpoint

use seq.midpoint

use seq.modExports

use standard

use seq.symbol

use symbol2

use seq.symdef

use set.symdef

use textio

use seq.seq.word

use set.word

Function libname(info:midpoint)word extractValue(first.src.info, "Library")_1

function makeentry(libraryuses:seq.word, entrypointname:word, input:seq.byte)seq.byte
let entryheader = 
 "use standard 
 /p use file 
 /p use inputoutput 
 /p use seq.file 
 /p use process.UTF8 
 /p Function entrypoint(args:UTF8)UTF8 
 /br let p=process.entrypoint2(args)
 /br if aborted.p then 
 /br finishentry.[file($(dq."error.html"), message.p)]
 /br else result.p 
 /p function entrypoint2(args0:UTF8)UTF8 
 /br let args=towords.args0 
 /br finishentry.$([entrypointname])(args, getfiles.args)
 /p Function $([entrypointname])(args:seq.word, input:seq.file)seq.file 
 /br let cmd=first.args 
 /br"
let finalclause = 
 if isempty.libraryuses then"empty:seq.file"
 else"$([merge(subseq(libraryuses, 1, 1) + "$EP")])(args, input)"
for acc = ""
, modname = "?"_1
, mods = if finalclause = "empty:seq.file"then""else[first.finalclause]
, p ∈ breakparagraph.input
do
 if subseq(p, 1, 1) = "Function" ∧ subseq(p, 3, 8) = "(input:seq.file"then
  let idx = findindex(")"_1, p)
  next(for para = ""
  , name = ", "_1
  , last = ", "_1
  , type = ""
  , w ∈ subseq(p, 10, idx)
  do
   if w ∈ ", )"then
    next(para
    + if type = "seq.word"then", extractValue(args, $(dq.[name]))"
    else if type = "boolean"then", first.$(dq.[name])∈ extractValue(args, $(dq."flags"))"
    else", ?"
    , name
    , w
    , ""
    )
   else if last ∈ ":"then next(para, name, last, type + w)
   else if last ∈ ", "then next(para, w, w, "")else next(para, name, w, type)
  /for(acc + " /br else if cmd /in $(dq.subseq(p, 2, 2))then $(subseq(p, 2, 2))(input $(para))")
  , modname
  , mods + modname
  )
 else if length.p > 1 ∧ p_1 ∈ "Module"then next(acc, p_2, mods)
 else next(acc, modname, mods)
/for(let uses = 
 for uses = "", u ∈ toseq.asset.mods do uses + "use" + u + " /p"/for(uses)
[tobyte.10, tobyte.10]
+ toseqbyte.textformat(uses + entryheader + acc << 2 + " /br else" + finalclause))

Function libsrc(input:seq.file, uses:seq.word, exports:seq.word, o:seq.word)seq.file
let Library = subseq(o, 1, 1)
for acc = empty:seq.byte, names = "parts=", f ∈ input do
 if ext.fn.f ∈ "ls libsrc"then next(acc + tobyte.10 + tobyte.10 + data.f, names + fullname.fn.f)
 else next(acc, names)
/for(let firstpart = 
 if isempty.exports then
  toseqbyte.toUTF8(names + "uses=$(uses)exports=$(exports)Library=$(Library)")
 else
  let entrypointname = merge(Library + "$EP")
  toseqbyte.toUTF8(names + "uses=$(uses)exports=$(exports + entrypointname)Library=$(Library)")
  + tobyte.10
  + tobyte.10
  + toseqbyte.toUTF8("Module" + entrypointname)
  + makeentry(uses, entrypointname, acc)
[file(filename(Library + ".libsrc"), firstpart + acc)])

function stacktracesymbol2 symbol symbol(moduleref."* debuginfo", "stacktraceimp", seqof.typeword)

function stacktracesymbol(allsrc:seq.seq.word)symbol
let libname = first.extractValue(first.allsrc, "Library")
let uses = extractValue(first.allsrc, "uses")
let baselib = if isempty.uses then libname else last.uses
symbol(moduleref([baselib] + "debuginfo"), "stacktraceimp", seqof.typeword)

function subcompilelib(allsrc:seq.seq.word, dependentlibs:midpoint)seq.file
{OPTION PROFILE}
let libname = extractValue(first.allsrc, "Library")
let uses = extractValue(first.allsrc, "uses")
let stacktracesymbol = stacktracesymbol.allsrc
let m = starmap.compilerfront2:libllvm("all2", allsrc, dependentlibs, stacktracesymbol)
let m2 = outlib.m
let dp = if isempty.uses then uses else[last.uses]
let files = compilerback(m, dependentwords.dp, stacktracesymbol)
files + file(filename(libname + ".libinfo"), outbytes:midpoint([m2]))

Function makebitcode(input:seq.file)seq.file
let info = breakparagraph.data.first.input
let libname = extractValue(first.info, "Library")
let uses = extractValue(first.info, "uses")
let dep = 
 for mp = empty:midpoint, i ∈ input << 1 do
  let new = first.inbytes:midpoint(data.i)
  midpoint("", prg.mp ∪ prg.new, emptytypedict, libmods.mp + libmods.new, empty:seq.seq.word)
 /for(mp)
let p = process.subcompilelib(info, dep)
if aborted.p then
 [file("error.html", "COMPILATION ERROR in libray:" + libname + EOL + message.p)
 ]
else result.p

function outlib(m:midpoint)midpoint
let libname = extractValue(first.src.m, "Library")
let libcode = asset.libcode.m
for acc = empty:seq.symdef, sd ∈ toseq.prg.m do
 if isabstract.module.sym.sd ∨ isconst.sym.sd ∨ isBuiltin.sym.sd ∨ isGlobal.sym.sd then acc
 else acc + symdef(sym.sd, removeFref.getCode(libcode, sym.sd), paragraphno.sd)
/for(for acc2 = acc, sd2 ∈ toseq(libcode \ asset.acc)do acc2 + symdef(sym.sd2, removeFref.code.sd2, 0)/for(midpoint("X", asset.acc2, empty:set.symdef, emptytypedict, libmods.m, empty:seq.seq.word)))

function removeFref(code:seq.symbol)seq.symbol
for codeNoFref = empty:seq.symbol, sy ∈ code do
 if isFref.sy then codeNoFref + PreFref + basesym.sy else codeNoFref + sy
/for(codeNoFref)

Function compilerFront(option:seq.word, allsrc:seq.seq.word)midpoint
{OPTION PROFILE}compilerfront2:libllvm(option, allsrc, empty:midpoint, stacktracesymbol.allsrc)

Function compilerFront(option:seq.word, input:seq.file)midpoint
{OPTION PROFILE}
for mp = empty:midpoint, data = empty:seq.byte, i ∈ input do
 if ext.fn.i ∈ "libinfo"then
  let new = first.inbytes:midpoint(data.i)
  next(midpoint("", prg.mp ∪ prg.new, emptytypedict, libmods.mp + libmods.new, empty:seq.seq.word)
  , data
  )
 else next(mp, data + [tobyte.10, tobyte.10] + data.i)
/for(let allsrc = breakparagraph.data
compilerfront2:libllvm(option, breakparagraph.data, mp, stacktracesymbol.allsrc))

Function modsE(ci:midpoint)seq.modExports libmods.ci

Export prg(ci:midpoint)set.symdef

function callfunc:libllvm(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int callfunc(ctsym, typedict, stk)

_______________

Export type:libllvm

type libllvm is a:int 