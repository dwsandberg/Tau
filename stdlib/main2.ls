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

use inputoutput

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

function makeentry(input:seq.byte)seq.byte
let entryheader = 
 "use standard /p use file /p use inputoutput /p use seq.file
/p use process.UTF8
/p
Function entrypoint(args:UTF8)UTF8
/br let p=process.entrypoint2(args)
/br if aborted.p then
/br   finishentry.[file($(dq."error.html"),message.p)] 
/br else  result.p 
/p Function entrypoint2(args0:UTF8)UTF8
/br let args = towords.args0 
/br finishentry.entrypoint1(args,getfiles.args)
/p Function entrypoint1(args:seq.word,input:seq.file) seq.file
/br let cmd=first.args
/br"
for acc = "", modname = "?"_1, mods = "", p ∈ breakparagraph.input do
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
    else if type = "boolean"then
     ", first.$(dq.[name])∈ extractValue(args, $(dq."flags"))"
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
+ toseqbyte.textformat(uses + entryheader + acc << 2 + " /br else empty:seq.file"))

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
  + makeentry.acc
[file(filename(Library + ".libsrc"), firstpart + acc)])

function subcompilelib(allsrc:seq.seq.word, dependentlibs:midpoint)seq.file
{OPTION PROFILE}
let uses = extractValue(first.allsrc, "uses")
let m = compilerfront2:libllvm("all2", allsrc, dependentlibs)
let libcode = libcode.m
let m2 = outlib(libcode, prg.m, libmods.m)
let bc = compilerback(m, {toseq.prg.m2}libcode, dependentwords.uses)
let libname = extractValue(first.allsrc, "Library")
[file(filename(libname + ".bc"), bc)
, file(filename(libname + ".libinfo"), outbytes:midpoint([m2]))
]

Function stdlib(input:seq.file)seq.file
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

function outlib(libcode0:seq.symdef, prg:set.symdef, libmods:seq.modExports)midpoint
let libcode = asset.libcode0
for acc = empty:seq.symdef, sd ∈ toseq.prg do
 if isabstract.module.sym.sd ∨ isconst.sym.sd ∨ isBuiltin.sym.sd ∨ isGlobal.sym.sd then acc
 else acc + symdef(sym.sd, removeFref.getCode(libcode, sym.sd), length.acc + 1)
/for(for acc2 = acc, sd2 ∈ toseq(libcode \ asset.acc)do acc2 + symdef(sym.sd2, removeFref.code.sd2, 0)/for(midpoint("X", asset.acc2, empty:set.symdef, emptytypedict, libmods, empty:seq.seq.word)))

function removeFref(code:seq.symbol)seq.symbol
for codeNoFref = empty:seq.symbol, sy ∈ code do
 if isFref.sy then codeNoFref + PreFref + basesym.sy else codeNoFref + sy
/for(codeNoFref)

Function compilerFront(option:seq.word, allsrc:seq.seq.word)midpoint
{OPTION PROFILE}compilerfront2:libllvm(option, allsrc, empty:midpoint)

Function compilerFront(option:seq.word, input:seq.file)midpoint
{OPTION PROFILE}
for mp = empty:midpoint, data = empty:seq.byte, i ∈ input do
 if ext.fn.i ∈ "libinfo"then
  let new = first.inbytes:midpoint(data.i)
  next(midpoint("", prg.mp ∪ prg.new, emptytypedict, libmods.mp + libmods.new, empty:seq.seq.word)
  , data
  )
 else next(mp, data + [tobyte.10, tobyte.10] + data.i)
/for(compilerfront2:libllvm(option, breakparagraph.data, mp))

Function modsE(ci:midpoint)seq.modExports libmods.ci

Export prg(ci:midpoint)set.symdef

function callfunc:libllvm(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int callfunc(ctsym, typedict, stk)

_______________

Export type:libllvm

type libllvm is a:int 